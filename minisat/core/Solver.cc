/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "minisat/mtl/Sort.h"
#include "minisat/core/Solver.h"
#include "minisat/utils/System.h"



#if 0
#define DEBUG_PRINTF printf
#else
#define DEBUG_PRINTF(...) \
    do {                  \
    } while (0)
#endif

using namespace Minisat;

//=================================================================================================
// Options:


static const char *_cat = "CORE";

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor", 0.95,
                                  DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999,
                                     DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq",
                                        "The frequency with which the decision heuristic tries to choose a random variable",
                                        0, DoubleRange(0, true, 1, true));
static IntOption opt_random_seed(_cat, "rnd-seed",
                                 "Used by the random variable selection",
                                 92702102, IntRange(0, INT_MAX));
static IntOption opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)",
                                0, IntRange(0, 2));
static IntOption opt_phase_saving(_cat, "phase-saving",
                                  "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static BoolOption opt_only_propagate(_cat, "only-propagate", "Use only polynomial algorithm. (only propagation) ", false);
static BoolOption opt_luby_restart(_cat, "luby", "Use the Luby restart sequence", true);
static BoolOption opt_is_opb(_cat, "opb", "Use opb input format", false);
static IntOption opt_restart_first(_cat, "rfirst", "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption opt_restart_inc(_cat, "rinc", "Restart interval increase factor", 2,
                                    DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption opt_garbage_frac(_cat, "gc-frac",
                                     "The fraction of wasted memory allowed before a garbage collection is triggered",
                                     0.20, DoubleRange(0, false, HUGE_VAL, false));

/* ================== LeqWatcher ================== */
//! watcher for LEQ clauses
struct Solver::PbWatcher {
    //! bound of the LEQ
    uint32_t coeff: 22; // TODO is it ok 15?
    //! number of lits in the LEQ
    uint32_t size: 10;

    CRef cref;

//    //! offset of the corresponding LeqStatus in ClauseAllocator
//    CRef status_ref() const {
//        return cref + size + LeqStatus::OFFSET_IN_CLAUSE;
//    }
//
//    LeqStatus& status(ClauseAllocator& ca) const {
//        return *ca.lea_as<LeqStatus>(status_ref());
//    }
//
//    //! LEQ = 0 <=> (nr_true >= bound_true)
//    int bound_true() const { return bound + 1; }
//
//    //! LEQ = 1 <=> (nr_false >= bound_false)
//    int bound_false() const { return size - bound; }
};

bool Solver::WatcherRefreshPb::operator()(PbWatcher& w) const {
    const Clause& c = ca[w.cref];
    if (c.mark() == 1) {
        // clause has been deleted
        return true;
    }
    // refresh size and bound to handle clause shrink
    if (w.size != c.size()) {
        // TODO maybe add something
        w.size = c.size();
    }
    return false;
}

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

// Parameters (user settable):
//
        verbosity(0),
        var_decay(opt_var_decay),
        clause_decay(opt_clause_decay),
        random_var_freq(opt_random_var_freq),
        random_seed(opt_random_seed),
        luby_restart(opt_luby_restart),
        ccmin_mode(opt_ccmin_mode),
        phase_saving(opt_phase_saving),
        rnd_pol(false),
        rnd_init_act(opt_rnd_init_act),
        only_propagate(opt_only_propagate),
        is_opb(opt_is_opb),
        garbage_frac(opt_garbage_frac),
        restart_first(opt_restart_first),
        restart_inc(opt_restart_inc)

        // Parameters (the rest):
        //
        ,
        learntsize_factor((double) 1 / (double) 3),
        learntsize_inc(1.1)

        // Parameters (experimental):
        //
        ,
        learntsize_adjust_start_confl(100),
        learntsize_adjust_inc(1.5)

        // Statistics: (formerly in 'SolverStats')
        //
        ,
        solves(0),
        starts(0),
        decisions(0),
        rnd_decisions(0),
        propagations(0),
        conflicts(0),
        dec_vars(0),
        clauses_literals(0),
        learnts_literals(0),
        max_literals(0),
        tot_literals(0),
        ok(true),
        cla_inc(1),
        var_inc(1),
        watches(WatcherDeleted(ca)),
        pb_watches{WatcherRefreshPb(ca)},
        qhead(0),
        simpDB_assigns(-1),
        simpDB_props(0),
        order_heap(VarOrderLt(activity)),
        progress_estimate(0),
        remove_satisfied(true),
        conflict_budget(-1)

        // Resource constraints:
        //
        ,
        propagation_budget(-1),
        asynch_interrupt(false),
        random_state{static_cast<uint64_t>(opt_random_seed)} {}


Solver::~Solver() {
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar) {
    int v = nVars();
    watches.init(mkLit(v, false));
    watches.init(mkLit(v, true));
    pb_watches.init(mkLit(v, false));
    pb_watches.init(mkLit(v, true));
    assigns.push(l_Undef);
    vardata.push(mkVarData(CRef_Undef, 0, 0));
    //activity .push(0);
    activity.push(rnd_init_act ? random_state.uniform() * 0.00001 : 0);
//    activity.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen.push(0);
    polarity.push(sign);
    decision.push();
    trail.capacity(v + 1);
    trail_delta_sum.capacity(v + 1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit> &ps) {
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:

    // We can skip sorting small clauses:
    // * 1 is always sorted!
    // * 2 is not always sorted, but for the unique-like loop below,
    //   it is good enough.
    if (ps.size() > 2) {
        sort(ps);
    }
    Lit p = lit_Undef;
    auto i = ps.begin();
    auto j = ps.begin();
    auto end = ps.end();
    while (i != end) {
        if (value(*i) == l_True || *i == ~p) {
            return true;
        } else if (value(*i) != l_False && *i != p) {
            *j = p = *i;
            ++j;
        }
        ++i;
    }
    ps.truncate(j);

    if (ps.empty()) {
        return ok = false;
    } else if (ps.size() == 1) {
        assert(decisionLevel() == 0);
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}

bool Solver::addLeqAssign_(vec<Term> &terms, int& bound) {
    for (auto &term: terms) {
        term.coeff *= -1;
    }
    bound *= -1;
    return addGeqAssign_(terms, bound);
}


bool Solver::addGeqAssign_(vec<Term> &terms, int& bound) {
    // We don't support adding learned pseudo boolean constraints
    if (terms.size() == 1) {
        printf("ddd");
    }
    assert(decisionLevel() == 0);
    if (!ok)
        return false;
    canonize_geq_clause(terms, bound);
    int sum = get_max_sum(terms);
    if (auto r = try_geq_clause_const_prop(terms, bound, sum); r.has_value()) {
        return r.value() and propagate() == CRef_Undef;
    }
    assert(bound > 0 && bound <= sum);
    weakening(terms, bound, sum);
    add_geq_and_setup_watchers(terms, bound, sum);
    if (propagate() != CRef_Undef) { // что-то стремное TODO думай
        return ok = false;
    }
    return true;
}

int Solver::get_max_sum(vec<Term> &terms) {
    int sum = 0;
    for (auto &term: terms) {
        sum += term.coeff;
    }
    return sum;
}

void Solver::canonize_geq_clause(vec<Term> &terms, int &bound) {
    sort(terms, [](Term a, Term b) { return a.lit < b.lit; });
    glue(terms, bound);
    make_positive(terms, bound);
    // TODO weekness: mix(bound, coeff), bound > 0
}

void Solver::make_positive(vec<Term> &terms, int &bound) {
    int i, j;
    for (i = 0, j = 0; i < terms.size(); i++) {
        if (value(terms[i].lit) == l_True) {
            bound -= terms[i].coeff;
            continue;
        }
        if (value(terms[i].lit) == l_False) {
            continue;
        }
        if (terms[i].coeff < 0) {
            terms[i].coeff *= -1;
            bound += terms[i].coeff;
            terms[i].lit = ~terms[i].lit;
        }
        if (terms[i].coeff != 0) {
            terms[j++] = terms[i];
            continue;
        } else {

        }
    }
    terms.shrink(i - j);
}

void Solver::glue(vec<Term> &terms, int &bound) {
    int i, j;
    for (i = 1, j = 0; i < terms.size(); i++) {
        if (var(terms[i].lit) == var(terms[j].lit)) {
            // possible options
            // 1) x_i; x_i
            // 2) x_i; not x_i
            // 3) not x_i; not x_i
            if (terms[i].lit == terms[j].lit) {
                terms[j].coeff += terms[i].coeff;
            } else {
                assert(sign(terms[i].lit) == true and sign(terms[j].lit) == false);
                bound -= terms[i].coeff;
                terms[j].coeff -= terms[i].coeff;
            }
        } else {
            terms[++j] = terms[i];
        }
    }
    terms.shrink(i - j - 1); // TODO double check
}

Minisat::optional<bool> Solver::try_geq_clause_const_prop(vec<Term> &terms, int &bound, int &sum) {

    if (bound <= 0) {
        return {ok = true};
    } else if (bound > sum) {
        return {ok = false};
    }
    int i, j;
    for (i = j = 0; i < terms.size(); i++) {
        if (sum - bound - terms[i].coeff < 0) {
            uncheckedEnqueue(terms[i].lit);
            bound -= terms[i].coeff;
            sum -= terms[i].coeff;
        } else {
            terms[j++] = terms[i];
        }
    }
    terms.shrink(i - j);
    if (j == 0 || bound <= 0) {
        return {ok = true}; // TODO double check
    }
    return {};
}

void Solver::add_geq_and_setup_watchers(vec<Term> &terms, int bound, int sum) {
//    constexpr int MAX_LEQ_SIZE = (1 << 7) - 10;
//    minisat_uassert(terms.size() < MAX_LEQ_SIZE, "LEQ too large: get %d, max %d",
//                    terms.size(), MAX_LEQ_SIZE);
    sort(terms, [](Term a, Term b) { return a.coeff > b.coeff; });
    CRef cr = ca.alloc(terms, bound, sum);
    clauses.push(cr);
//    assert(ca.ael(&ca[cr].leq_status()) - cr ==
//           ps.size() + LeqStatus::OFFSET_IN_CLAUSE);

    // note that duplicated lits are naturally handled by adding multiple
    // watchers

    for (int i = 0; i < terms.size(); ++i) {
        Lit p = terms[i].lit;
        minisat_uassert(terms[i].coeff < (1 << 22), "coefficients should be less than 2^22");
        minisat_uassert(terms.size() < (1 << 10), "size should be less than 2^10");
        PbWatcher watcher = {
                .coeff = static_cast<uint32_t>(terms[i].coeff),
                .size = static_cast<uint32_t>(terms.size()),
                .cref = cr,
        };
        pb_watches[~p].push(watcher);
    }

    clauses_literals += terms.size();
}

void Solver::attachClause(CRef cr) {
    const Clause &c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict) {
    const Clause &c = ca[cr];
    assert(c.size() > 1);

    if (strict) {
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    } else {
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause &c = ca[cr];
    if (c.is_pb()) {
        assert(decisionLevel() == 0);
        for (int i = 0, it = c.size(); i < it; ++i) {
//            printf("megadeth\n");
            Lit l = c[i];
            // remove watcher
            pb_watches.smudge(~l);
            // remove self reason reference
            CRef& reason = vardata[var(l)].reason;
            if (reason == cr) {
                reason = CRef_Undef;
            }
        }
    } else {
        detachClause(cr);
        // Don't leave pointers to free'd memory!
        if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    }
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause &c) const {
    if (c.is_pb()) {
        int curr_sum = 0;
        for (int i = 0; i < c.size(); i++) {
            if (value(c[i]) == l_True) {
                curr_sum += c.get_coeff(i);
            }
        }
        return curr_sum >= c.bound();
    }
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false;
}


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level) {
        int ind;
        for (ind = trail_delta_sum.size() - 1;  ind >= 0 and trail_delta_sum[ind].level > level; ind--) {
            DeltaData last = trail_delta_sum[ind];
            Clause& clause = ca[last.clause];
            assert(clause.is_pb());
            clause.del() -= last.delta;
            assert(clause.sum() >= 0);
        }

        for (int c = trail.size() - 1; c >= trail_lim[level]; c--) {
            Var x = var(trail[c]);
            assigns[x] = l_Undef;

            if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail_delta_sum.shrink(trail_delta_sum.size() - ind - 1); // TODO make more elegant
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:

//
//Lit Solver::pickBranchLit() {
//    Var next = var_Undef;
//
//    // Random decision:
//    if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
//        next = order_heap[irand(random_seed, order_heap.size())];
//        if (value(next) == l_Undef && decision[next])
//            rnd_decisions++;
//    }
//
//    // Activity based decision:
//    while (next == var_Undef || value(next) != l_Undef || !decision[next])
//        if (order_heap.empty()) {
//            next = var_Undef;
//            break;
//        } else
//            next = order_heap.removeMin();
//
//    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
//}

//=================================================================================================
// Major methods:

Lit Solver::pickBranchLit() {
    Var next = var_Undef;

    // Random decision:
    if (random_var_freq && !order_heap.empty() &&
        random_state.binomial(random_var_freq)) {
        next = order_heap[random_state.randint(order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++;
    }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()) {
            return lit_Undef;
        } else {
            next = order_heap.removeMin();
        }
    }

    bool sign = rnd_pol ? random_state.binomial(0.5) : polarity[next];
//    DEBUG_PRINTF("branch var=%d sign=%d act=%.3f\n", next + 1,
//                  sign, activity[next]);
    DEBUG_PRINTF("branch var=%d\n", next + 1);
    return mkLit(next, sign);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit> &out_learnt, int &out_btlevel) {
    int pathC = 0;
    Lit p = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index = trail.size() - 1;
    assert(index > 0);
//    printTrail(20);
    auto add_antecedent = [&](Lit q) __attribute__((always_inline)) {
        // add ~q as a visited antecident (in the graph it is ~q, and q is added
        // to the learnt clause)

        if (!seen[var(q)] && level(var(q)) > 0) {
            varBumpActivity(var(q));
            seen[var(q)] = 1;
            if (level(var(q)) >= decisionLevel()) {
                // Only the decision var at current level should be added to the
                // learnt clause. We keep a counter here instead of adding the
                // var, so it would be processed later.
                pathC++;
//                printf("%d\n", var(q) + 1);
            } else {
                out_learnt.push(q);
            }
        }
    };

    do {
//        printClauses(confl);
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause &c = ca[confl];

//        printClauses(confl);

        if (c.is_pb()) {
            int sum = 0;
            for (int i = 0; i < c.size(); i++) {
                if (value(c[i]) == l_False and pos(var(c[i])) <= index) {
                    if (c.sum() - sum < c.bound())
                        break;
                    sum += c.get_coeff(i);
                    add_antecedent(c[i]);
                }
            }
        } else {
            if (c.learnt())
                claBumpActivity(c);

            for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
                add_antecedent(c[j]);
            }
        }
        // Select next clause to look at:
//        while ( and pathC > 0) { TODO
            while (!seen[var(trail[index--])]) {
                assert(index >= 0);
            }
            p = trail[index + 1];
//            DEBUG_PRINTF("%d\n", var(p));
            confl = reason(var(p));
            seen[var(p)] = 0; // Почему это нужно в minisat и а что у нас?
            pathC--;
//        }
    } while (pathC > 0);
    out_learnt[0] = ~p;

//    if (out_learnt.size() == 1) {
//
//    }

    assert(level(var(p)) == decisionLevel());

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2) {
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(
                    var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    } else if (ccmin_mode == 1) {
        for (i = j = 1; i < out_learnt.size(); i++) {
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause &c = ca[reason(var(out_learnt[i]))];
                if (c.is_pb()) {
                    // TODO
                } else {
                    for (int k = 1; k < c.size(); k++)
                        if (!seen[var(c[k])] && level(var(c[k])) > 0) {
                            out_learnt[j++] = out_learnt[i];
                            break;
                        }
                }
            }
        }
    } else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        int max_idx = 1;
        int min_lvl = level(var(out_learnt[1]));
        // Find the first literal assigned at the next-highest level:
        for (int idx = 2; idx < out_learnt.size(); idx++) {
            if (level(var(out_learnt[idx])) > min_lvl) {
                min_lvl = level(var(out_learnt[idx]));
                max_idx = idx;
            }
        }
        // Swap-in this literal at index 1:
        Lit temp = out_learnt[max_idx];
        out_learnt[max_idx] = out_learnt[1];
        out_learnt[1] = temp;
        out_btlevel = min_lvl;
    }

//    if (out_learnt.size() != before_out_learnt_size && out_learnt.empty()) {
//        printf("%d %d \n", out_learnt.size(), before_out_learnt_size);
//        assert(false);
//    }

    for (auto const &elem: analyze_toclear) {
        seen[var(elem)] = 0;
    }
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0) {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause &c = ca[reason(var(analyze_stack.last()))];
        analyze_stack.pop();

        if (c.is_pb()) {
            return false;
            // TODO
        } else {
            for (int i = 1; i < c.size(); i++) {
                Lit cp = c[i];
                if (!seen[var(cp)] && level(var(cp)) > 0) {
                    if (reason(var(cp)) != CRef_Undef && (abstractLevel(var(cp)) & abstract_levels) != 0) {
                        seen[var(cp)] = 1;
                        analyze_stack.push(cp);
                        analyze_toclear.push(cp);
                    } else {
                        for (int j = top; j < analyze_toclear.size(); j++)
                            seen[var(analyze_toclear[j])] = 0;
                        analyze_toclear.shrink(analyze_toclear.size() - top);
                        return false;
                    }
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit> &out_conflict) {
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            } else {
                Clause &c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from) {
    assert(value(p) == l_Undef);
    if (var(p) == 8293) {

    }
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel(), trail.size());
    trail.push_(p);
//    DEBUG_PRINTF("enqueue var=%d sign=%d is_assumption=%d dl=%d\n", var(p) + 1,
//                 sign(p), from==CRef_Undef, decisionLevel());
    DEBUG_PRINTF("enqueue var=%d\n", var(p) + 1);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate() {
    CRef confl = CRef_Undef;
    int num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
//        printf("up %d\n", p.x);
        if (var(p) == 4128 - 1 and decisionLevel() > 100) {

        }
        vec<Watcher> &ws = watches[p];
        Watcher *i, *j, *end;
        num_props++;

        for (i = j = (Watcher *) ws, end = i + ws.size(); i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True) {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = i->cref;
            Clause &c = ca[cr];
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            if (first != blocker && value(first) == l_True) {
                *j++ = w;
                continue;
            }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False) {
                confl = cr;
//                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            } else {
                uncheckedEnqueue(first, cr);
            }

            NextClause:;
        }
        ws.truncate(j);

        if (confl == CRef_Undef) {
            confl = propagate_pb(p);
        }
        if (confl != CRef_Undef) {
            break;
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

CRef Minisat::Solver::propagate_pb(Lit new_fact) {
    const vec<PbWatcher> &watches_list = pb_watches[new_fact];
    int watcher_size = watches_list.size();
    for (int watcher_idx = 0; watcher_idx < watcher_size; ++watcher_idx) {
        const PbWatcher watch = watches_list[watcher_idx];
        CRef cref = watch.cref;

        assert (cref != vardata[var(new_fact)].reason);
        assert (ca[cref].is_pb());

        Clause &c = ca[cref];
        if (c.mark() == 1) {
            // The clause has been removed, but not reclaimed. This happens
            // during simplyfication
            assert(decisionLevel() == 0);
            continue;
        }
        assert(c.is_pb());
        int &bound = c.bound();
        int &del = c.del();
        assert(c.sum() - del >= watch.coeff);
        del += watch.coeff;
        assert(del > 0);
        assert(del <= c.sum());
//        if (cref == 434553) {
//
//        }
        trail_delta_sum.push({cref, watch.coeff, decisionLevel()});


        if (c.sum() - del < bound) {
            // conflict
            return cref; // ну и в чем смысл. Мем
        }

        for (int i = 0; i < c.size(); i++) {
            if (value(c[i]) == l_Undef) {
                if (c.sum() - del - bound - c.get_coeff(i) < 0) {
                    uncheckedEnqueue(c[i], cref);
                } else {
                    break;
                }
            }
        }
    }
    return CRef_Undef;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
namespace {
    struct reduceDB_lt {
        ClauseAllocator &ca;

        reduceDB_lt(ClauseAllocator &ca_) : ca(ca_) {}

        bool operator()(CRef x, CRef y) {
            return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
        }
    };
}

void Solver::reduceDB() {
//    printf("deth\n");
    int i, j;
    double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++) {
        Clause &c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef> &cs) {
    int i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause &c = ca[cs[i]];
        if (satisfied(c) || try_geq_simplify(c)) {
            removeClause(cs[i]);
        } else {
            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap() {
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify() {
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied) {    // Can be turned off.
        removeSatisfied(clauses);



        // we will never need to backtrace below 0, so it's safe to clear the
        // stats;
        trail_delta_sum.clear();

        pb_watches.cleanAll();
        // need delete dead var
    }

    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts) {
    assert(ok);
    int backtrack_level;
    int conflictC = 0;
    vec<Lit> learnt_clause;
    starts++;

    for (;;) {
        CRef confl = propagate();
        if (confl != CRef_Undef) {
            // CONFLICT
            conflicts++;
            conflictC++;
            if (decisionLevel() == 0) {
                return l_False;
            }

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            if (learnt_clause.size() == 1) {
                assert(decisionLevel() == 0);
                uncheckedEnqueue(learnt_clause[0]);
            } else {
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                assert(decisionLevel() != 0);
//                printClauses(confl);
//                printClauses(cr);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0) {
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt = (int) learntsize_adjust_confl;
                max_learnts *= learntsize_inc;

                if (verbosity >= 1)
                    fprintf(stderr, "| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                            (int) conflicts,
                            (int) dec_vars - (trail_lim.empty() ? trail.size() : trail_lim[0]), nClauses(),
                            (int) clauses_literals,
                            (int) max_learnts, nLearnts(), (double) learnts_literals / nLearnts(),
                            progressEstimate() * 100);
            }

        } else {
            // NO CONFLICT
            if (nof_conflicts >= 0 && (conflictC >= nof_conflicts || !withinBudget())) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size() - nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            assert(decisionLevel() != 0);
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const {
    double progress = 0;
    double F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x) {

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);

    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_() {
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    learntsize_adjust_confl = learntsize_adjust_start_confl;
    learntsize_adjust_cnt = (int) learntsize_adjust_confl;
    lbool status = l_Undef;

    if (verbosity >= 1) {
        fprintf(stderr, "============================[ Search Statistics ]==============================\n");
        fprintf(stderr, "| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        fprintf(stderr, "|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        fprintf(stderr, "===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef) {
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(static_cast<int>(rest_base * restart_first));
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        fprintf(stderr, "===============================================================================\n");


    if (status == l_True) {
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    } else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var> &map, Var &max) {
    if (map.size() <= x || map[x] == -1) {
        map.growTo(x + 1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE *f, Clause &c, vec<Var> &map, Var &max) {
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max) + 1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit> &assumps) {
    FILE *f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE *f, const vec<Lit> &) {
    // Handle case when solver is in contradictory state:
    if (!ok) {
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return;
    }

    vec<Var> map;
    Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (auto const &clause: clauses) {
        if (!satisfied(ca[clause])) {
            ++cnt;
        }
    }

    for (auto const &clause: clauses) {
        if (!satisfied(ca[clause])) {
            Clause &c = ca[clause];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }
    }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (auto const &assump: assumptions) {
        assert(value(assump) != l_False);
        fprintf(f, "%s%d 0\n", sign(assump) ? "-" : "", mapVar(var(assump), map, max) + 1);
    }

    for (auto const &cl: clauses) {
        toDimacs(f, ca[cl], map, max);
    }

    if (verbosity > 0)
        fprintf(stderr, "Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator &to) {
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    pb_watches.cleanAll();

    for (int v = 0; v < nVars(); v++) {
        for (int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            for (auto &w: watches[p]) {
                ca.reloc(w.cref, to);
            }

            for (PbWatcher& w : pb_watches[p]) {
                ca.reloc(w.cref, to);
            }
        }
    }

    // All reasons:
    //
    for (auto const &t: trail) {
        Var v = var(t);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All delta:
    //
    for (auto &t: trail_delta_sum) {
        ca.reloc(t.clause, to);
    }

    // All learnt:
    //
    for (auto &learnt: learnts) {
        ca.reloc(learnt, to);
    }

    // All original:
    //
    for (auto &cl: clauses) {
        ca.reloc(cl, to);
    }
}


void Solver::garbageCollect() {
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        fprintf(stderr, "|  Garbage collection:   %12d bytes => %12d bytes             |\n",
                ca.size() * ClauseAllocator::Unit_Size, to.size() * ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void Solver::printClauses() const {
    printf("-----------------------------------\n");
    for (auto clauseRef: clauses) {
        printClauses(clauseRef);
    }
    printf("-----------------------------------\n");
}

void Solver::printLearnt() const {
    printf("-----------------------------------\n");
    for (auto clauseRef: learnts) {
        printClauses(clauseRef);
    }
    printf("-----------------------------------\n");
}

void Solver::printClauses(CRef clauseRef) const {
    const Clause &clause = ca[clauseRef];
    if (clause.is_pb()) {
//        printf("clause: is_pb = %d, sum = %d del = %d \n", clause.is_pb(), clause.sum(), clause.del());
        int sum = 0;
        for (int i = 0; i < clause.size(); i++) {
//            printf("%d %sx%d ",
//                   clause.get_coeff(i),
//                   sign(clause[i]) ? "-" : "",
//                   var(clause[i]) + 1);
            printf("%s%d ",
                   sign(clause[i]) ? "-" : "",
                   var(clause[i]) + 1);
            sum += clause.get_coeff(i);
        }
//        printf(" >= %d", clause.bound());
        printf("\n");
//        printf("real sum = %d \n", sum);
    } else {
//            printf("clause: is_leg = %d  \n", clause.is_leq());
        for (int i = 0; i < clause.size(); i++) {
            printf("var=%sX_%d ",
                   sign(clause[i]) ? "-" : "", var(clause[i]) + 1);
        }
        printf("\n");
    }
}

void Solver::printLit(Lit li) const {
    printf("-----------------------------------\n");
    printf("var=%s%d ",
           sign(li) ? "-" : "", var(li) + 1);
    printf("\n");
    printf("-----------------------------------\n");
}

void Solver::printTrail(int lv) const {
    printf("-----------------------------------\n");
    int index = trail.size() - 1;
    while (index >= 0 && level(var(trail[index])) >= lv) {
        Lit q = trail[index];
        printf("lv %d \n", level(var(trail[index])));
        printf("%s%d X%d_%d: ", sign(q) ? "-" : "", var(q) + 1, (var(q)) / 4 + 1,  (var(q)) % 4 + 1);
        CRef res = reason(var(q));
        if (res == CRef_Undef) {
            printf("%s \n", "UNDEF");
        } else {
            const Clause &c = ca[res];
            for (int i = 0; i < c.size(); i++) {
                printf("%s%d ", sign(c[i]) ? "-" : "", var(c[i]) + 1);
            }
            printf("\n ");
        }
        index--;
    }
    printf("-----------------------------------\n");
}

void Solver::printTrailDeltaSum(CRef clauseRef) const {
    printf("-----------------------------------\n");
    printClauses(clauseRef);
    int sum = 0;
    for (auto& delta_sum: trail_delta_sum) {
        if (delta_sum.clause == clauseRef) {
            sum += delta_sum.delta;
            printf("delta = %d, level = %d\n", delta_sum.delta, delta_sum.level);
        }
    }
    printf("sum = %d\n", sum);
    printf("-----------------------------------\n");
}


void Solver::printTrailDeltaSum() const {
    printf("-----------------------------------\n");
    for (auto clauseRef: clauses) {
        printTrailDeltaSum(clauseRef);
    }
    printf("-----------------------------------\n");
}

bool Minisat::Solver::try_geq_simplify(Clause &c) {
    if (!c.is_pb()) {
        return false;
    }
    // TODO
    return false;
}
