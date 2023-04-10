/****************************************************************************************[Dimacs.h]
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

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

    template<class B, class Solver>
    static bool readClause(B &in, Solver &S, vec<Lit> &lits) {
        int parsed_lit;
        lits.clear();

        auto get_lit = [&S](int v) -> Lit {
            int var = abs(v) - 1;
            while (var >= S.nVars())
                S.newVar();
            return (v > 0) ? mkLit(var) : ~mkLit(var);
        };

        if (*in == '#') {
            // parse PB constraint.
            // expected format:
            // # -1 * 2  8 * 5 -3 * 1 >= 5
            //        <==>
            // # -1 * X_2 8 * X_5 -3 * X_1 >= 5
            ++in;

            vec<Term> terms;

            for (;;) {
                skipWhitespace(in);
                if (*in == '>' || *in == '<') {
                    // parse inequalities
                    char op = *in;
                    ++in;
                    if (*in != '=') {
                        fprintf(stderr,
                                "PARSE ERROR! Unexpected char in inequality: %c\n",
                                *in),
                                exit(3);
                    }
                    ++in;
                    int bound = parseInt(in);
                    skipWhitespace(in);
                    if (op == '<') {
                        S.addLeqAssign_(terms, bound);
                    } else {
                        S.addGeqAssign_(terms, bound);
                    }
                    return false;
                }
                int coefficient = parseInt(in);
                skipWhitespace(in);
                assert(*in == '*');
                ++in;
                parsed_lit = parseInt(in);
                terms.push(Term{coefficient, get_lit(parsed_lit)});
            }
        } else {
            // parse simple cnf
            for (;;) {
                parsed_lit = parseInt(in);
                if (parsed_lit == 0) break;
                lits.push(get_lit(parsed_lit));
            }
        }
        return true;
    }

    template<class B, class Solver>
    static void parse_DIMACS_main(B &in, Solver &S) {
        vec<Lit> lits;
        int vars = 0;
        int clauses = 0;
        int cnt = 0;
        for (;;) {
            skipWhitespace(in);
            if (*in == EOF) break;
            else if (*in == 'p') {
                if (eagerMatch(in, "p cnf")) {
                    vars = parseInt(in);
                    clauses = parseInt(in);
                    // SATRACE'06 hack
                    // if (clauses > 4000000)
                    //     S.eliminate(true);
                } else {
                    printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
                }
            } else if (*in == 'c' || *in == 'p')
                skipLine(in);
            else {
                cnt++;
                if (readClause(in, S, lits)) {
                    S.addClause_(lits);
                }
            }

        }
        if (vars != S.nVars())
            fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
        if (cnt != clauses)
            fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
    }

    template<class B, class Solver>
    static void parse_OPB_main(B &in, Solver &S) {
        int vars = 0;
        int clauses = 0;
        int cnt = 0;
        for (;;) {
            skipWhitespace(in);
            if (*in == EOF) break;
            else if (*in == '*') {
                skipLine(in);
            } else {
                cnt++;
                readPB(in, S);
            }

        }
        if (vars != S.nVars())
            fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
        if (cnt != clauses)
            fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
    }

    template<class B, class Solver>
    static void readPB(B &in, Solver &S) {
        vec<Lit> lits;
        lits.clear();

        auto get_lit = [&S](int v) -> Lit {
            int var = abs(v) - 1;
            while (var >= S.nVars())
                S.newVar();
            return (v > 0) ? mkLit(var) : ~mkLit(var);
        };


        // parse PB constraint.
        // expected format:
        // # -1 * 2  8 * 5 -3 * 1 >= 5
        //        <==>
        // # -1 * X_2 8 * X_5 -3 * X_1 >= 5

        vec<Term> terms;

        for (;;) {
            skipWhitespace(in);
            if (*in == EOF) break;
            if (*in == '>' || *in == '<') {
                // parse inequalities
                char op = *in;
                ++in;
                if (*in != '=') {
                    fprintf(stderr,
                            "PARSE ERROR! Unexpected char in inequality: %c\n",
                            *in),
                            exit(3);
                }
                ++in;
                int bound = parseInt(in);
                skipWhitespace(in);
                assert(*in == ';');
                ++in;
                if (op == '<') {
                    S.addLeqAssign_(terms, bound);
                } else {
                    S.addGeqAssign_(terms, bound);
                }
                return;
            } else if (*in == '=') {
                ++in;
                int bound = parseInt(in);
                skipWhitespace(in);
                assert(*in == ';');
                ++in;
                S.addGeqAssign_(terms, bound);
                S.addLeqAssign_(terms, bound);
                return;
            }
            int coefficient = parseInt(in);
            skipWhitespace(in);
            int parsed_lit = 1;
            if (*in == '-') {
                parsed_lit = -1;
                ++in;
            } else if (*in == '+') {
                parsed_lit = 1;
                ++in;
            }
            assert(*in == 'x');
            ++in;
            parsed_lit *= parseInt(in);
            terms.push(Term{coefficient, get_lit(parsed_lit)});
        }
    }


// Inserts problem into solver.
//
    template<class Solver>
    static void parse_DIMACS(FILE *input_stream, Solver &S) {
        StreamBuffer in(input_stream);
        parse_DIMACS_main(in, S);
    }

    template<class Solver>
    static void parse_OPB(FILE *input_stream, Solver &S) {
        StreamBuffer in(input_stream);
        parse_OPB_main(in, S);
    }

//=================================================================================================
}

#endif
