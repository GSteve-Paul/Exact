/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

/**********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**********************************************************************/

#pragma once

#include <string>
#include "typedefs.hpp"

namespace rs {

class Solver;

namespace parsing {

bigint read_bigint(const std::string& s, int start);
void file_read(Solver& solver);
void opb_read(std::istream& in, Solver& solver);
void cnf_read(std::istream& in, Solver& solver);
void wcnf_read(std::istream& in, Solver& solver);
void mps_read(const std::string& filename, Solver& solver);
void lp_read(const std::string& filename, Solver& solver);
template <typename T>
void coinutils_read(T& coinutils, Solver& solver, bool wasMaximization);

using RatVal = ratio;

struct IntVar {
  explicit IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub);

  [[nodiscard]] const std::string& getName() const { return name; }
  [[nodiscard]] const bigint& getUpperBound() const { return upperBound; }
  [[nodiscard]] const bigint& getLowerBound() const { return lowerBound; }

  [[nodiscard]] bigint getRange() const { return upperBound - lowerBound; }
  [[nodiscard]] bool isBoolean() const { return getRange() == 1; }

  bool usesLogEncoding() const { return logEncoding; }
  const std::vector<Var>& encodingVars() const { return encoding; }

 private:
  std::string name;
  bigint lowerBound;
  bigint upperBound;

  bool logEncoding;
  std::vector<Var> encoding;
};
std::ostream& operator<<(std::ostream& o, const IntVar& x);

struct IntTerm {
  RatVal c;
  IntVar* v;
  bool negated;

  IntTerm(const RatVal& val, IntVar* var, bool neg) : c(val), v(var), negated(neg) {}
};
std::ostream& operator<<(std::ostream& o, const IntTerm& x);

struct IntConstraint {
  std::vector<IntTerm> lhs;
  RatVal lowerBound = 0;
  bool lowerBoundSet = false;
  RatVal upperBound = 0;
  bool upperBoundSet = false;

  void normalize();
  void toConstrExp(CeArb&, bool useLowerBound) const;
  void setLowerBound(const RatVal& b) {
    lowerBoundSet = true;
    lowerBound = b;
  }
  void setUpperBound(const RatVal& b) {
    upperBoundSet = true;
    upperBound = b;
  }
};
std::ostream& operator<<(std::ostream& o, const IntConstraint& x);

struct ILP {
  Solver& solver;
  std::vector<std::unique_ptr<IntVar>> vars;
  std::vector<std::unique_ptr<IntConstraint>> constrs;
  IntConstraint obj;
  bigint objmult = 1;
  std::unordered_map<std::string, IntVar*> name2var;

  ILP(Solver& s) : solver(s){};

  IntConstraint* newConstraint();
  IntVar* getVarFor(const std::string& name, bool nameAsId = true, const bigint& lowerbound = 0,
                    const bigint& upperbound = 1);
  void addToSolver();
  void printOrigSol(const std::vector<Lit>& sol);
};
std::ostream& operator<<(std::ostream& o, const ILP& x);

}  // namespace parsing

}  // namespace rs
