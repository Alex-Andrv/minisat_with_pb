#include "minisat/core/Recorder.h"
#include "minisat/core/Solver.h"
#include "minisat/utils/System.h"

#include <signal.h>

#include <algorithm>
#include <condition_variable>
#include <cstring>
#include <functional>
#include <thread>
#include <vector>


class WrappedMinisatSolver : public Minisat::Solver {
public:
    void addClause(std::vector<int> lits) {
        Minisat::vec<Minisat::Lit> ps;
        for (int lit : lits) {
            ps.push(get_lit(lit));
        }
        addClause_(ps);
    }

    bool addLeqAssign(std::vector<int> lits, std::vector<int> coeff, int bound) {
        Minisat::vec<Minisat::Term> ps;
        assert(lits.size() == coeff.size());
        for (int i = 0; i < static_cast<int>(lits.size()); i++) {
            ps.push(Minisat::Term{coeff[i], get_lit(lits[i])});
        }
        addLeqAssign_(ps, bound);
    }

    bool addGeqAssign(std::vector<int> lits, std::vector<int> coeff, int bound) {
        Minisat::vec<Minisat::Term> ps;
        assert(lits.size() == coeff.size());
        for (int i = 0; i < static_cast<int>(lits.size()); i++) {
            ps.push(Minisat::Term{coeff[i], get_lit(lits[i])});
        }
        addGeqAssign_(ps, bound);
    }
private:
    Minisat::Lit get_lit(int lit) {
        int var = abs(lit) - 1;
        while (var >= nVars())
            newVar();
        return (lit > 0) ? Minisat::mkLit(var) : ~Minisat::mkLit(var);
    }
};
