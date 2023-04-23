#include "minisat/core/Solver.h"
#include <vector>

namespace Minisat {
    class WrappedMinisatSolver : public Minisat::Solver {
    public:
        bool addClause(std::vector<int> lits) {
            Minisat::vec<Minisat::Lit> ps;
            for (int lit: lits) {
                ps.push(get_lit(lit));
            }
            return addClause_(ps);
        }

        bool addLeqAssign(std::vector<int> lits, std::vector<int> coeff, int bound) {
            Minisat::vec<Minisat::Term> ps;
            assert(lits.size() == coeff.size());
            for (int i = 0; i < static_cast<int>(lits.size()); i++) {
                ps.push(Minisat::Term{coeff[i], get_lit(lits[i])});
            }
            return addLeqAssign_(ps, bound);
        }

        bool addGeqAssign(std::vector<int> lits, std::vector<int> coeff, int bound) {
            Minisat::vec<Minisat::Term> ps;
            assert(lits.size() == coeff.size());
            for (int i = 0; i < static_cast<int>(lits.size()); i++) {
                ps.push(Minisat::Term{coeff[i], get_lit(lits[i])});
            }
            return addGeqAssign_(ps, bound);
        }

        int prop(std::vector<int> assumps, int psaving) {
            Minisat::vec<Minisat::Lit> ps;
            for (int lit: assumps) {
                ps.push(get_lit(lit));
            }
            return prop_check(ps, psaving);
        }

    private:
        Minisat::Lit get_lit(int lit) {
            int var = abs(lit) - 1;
            while (var >= nVars())
                newVar();
            return (lit > 0) ? Minisat::mkLit(var) : ~Minisat::mkLit(var);
        }
    };
}