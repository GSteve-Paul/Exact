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
  bigint c;
  IntVar* v;
  bool negated;

  IntTerm(const bigint& val, IntVar* var, bool neg) : c(val), v(var), negated(neg) {}
};
std::ostream& operator<<(std::ostream& o, const IntTerm& x);

class IntConstraint {
  std::vector<IntTerm> lhs;
  std::optional<bigint> lowerBound;
  std::optional<bigint> upperBound;

  void normalize();

 public:
  IntConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars, const std::vector<bool>& negated,
                const std::optional<bigint>& lb = std::nullopt, const std::optional<bigint>& ub = std::nullopt);

  const std::vector<IntTerm>& getLhs() const { return lhs; }
  const std::optional<bigint>& getLB() const { return lowerBound; }
  const std::optional<bigint>& getUB() const { return upperBound; }

  void toConstrExp(CeArb&, bool useLowerBound) const;
};
std::ostream& operator<<(std::ostream& o, const IntConstraint& x);

struct ILP {
  Solver& solver;
  std::vector<std::unique_ptr<IntVar>> vars;
  std::vector<IntConstraint> constrs;
  IntConstraint obj;
  bigint objmult = 1;
  std::unordered_map<std::string, IntVar*> name2var;

  ILP(Solver& s) : solver(s), obj({}, {}, {}, 0) {}

  IntVar* getVarFor(const std::string& name, bool nameAsId = true, const bigint& lowerbound = 0,
                    const bigint& upperbound = 1);
  bool hasVarFor(const std::string& name) const;
  void addObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                    const std::vector<bool>& negated, const bigint& mult = 1, const bigint& offset = 0);
  State addConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                      const std::vector<bool>& negated, const std::optional<bigint>& lb = std::nullopt,
                      const std::optional<bigint>& ub = std::nullopt);

  void printOrigSol(const std::vector<Lit>& sol);
};
std::ostream& operator<<(std::ostream& o, const ILP& x);

}  // namespace parsing

}  // namespace rs
