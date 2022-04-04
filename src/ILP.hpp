/**********************************************************************
This file is part of Exact.

Copyright (c) 2022 Jo Devriendt

Exact is free software: you can redistribute it and/or modify it under
the terms of the GNU Affero General Public License version 3 as
published by the Free Software Foundation.

Exact is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public
License version 3 for more details.

You should have received a copy of the GNU Affero General Public
License version 3 along with Exact. See the file used_licenses/COPYING
or run with the flag --license=AGPLv3. If not, see
<https://www.gnu.org/licenses/>.
**********************************************************************/

/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include <string>
#include "Solver.hpp"
#include "typedefs.hpp"

namespace xct {

struct IntVar {
  explicit IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub);

  [[nodiscard]] const std::string& getName() const { return name; }
  [[nodiscard]] const bigint& getUpperBound() const { return upperBound; }
  [[nodiscard]] const bigint& getLowerBound() const { return lowerBound; }

  [[nodiscard]] bigint getRange() const { return upperBound - lowerBound; }
  [[nodiscard]] bool isBoolean() const { return lowerBound == 0 && upperBound == 1; }

  bool usesLogEncoding() const { return logEncoding; }
  const std::vector<Var>& encodingVars() const { return encoding; }
  bigint getValue(const std::vector<Lit>& sol) const;

 private:
  const std::string name;
  const bigint lowerBound;
  const bigint upperBound;

  const bool logEncoding;
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

struct UnsatState : public std::exception {
  const char* what() const throw() { return "Solver is in an UNSAT state."; }
};

class ILP {
  Solver solver;
  Optim optim;

  bool unsatDetected = false;

  std::vector<std::unique_ptr<IntVar>> vars;
  IntConstraint obj;
  bigint objmult = 1;
  std::unordered_map<std::string, IntVar*> name2var;
  std::unordered_map<Var, IntVar*> var2var;

  int maxSatVars = -1;

  std::vector<Lit> assumptions;  // TODO: pass assumptions to run() instead of keeping track of them here?

 public:
  ILP();

  const IntConstraint& getObjective() const { return obj; }
  Solver& getSolver() { return solver; }
  Optim getOptimization() { return optim; }
  void setMaxSatVars() { maxSatVars = solver.getNbVars(); }
  int getMaxSatVars() const { return maxSatVars; }

  IntVar* getVarFor(const std::string& name, bool nameAsId = true, const bigint& lowerbound = 0,
                    const bigint& upperbound = 1);
  bool hasVarFor(const std::string& name) const;
  std::vector<std::string> getVariables() const;
  std::pair<bigint, bigint> getBounds(const std::string& name) const;

  void setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                    const std::vector<bool>& negated, const bigint& mult = 1, const bigint& offset = 0);
  void setAssumptions(const std::vector<bigint>& vals, const std::vector<IntVar*>& vars);

  void init(bool boundObjective, bool addNonImplieds);
  SolveState run();
  SolveState runFull();

  State addConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                      const std::vector<bool>& negated, const std::optional<bigint>& lb = std::nullopt,
                      const std::optional<bigint>& ub = std::nullopt);
  State addReification(IntVar* head, const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const bigint& lb);
  State boundObjByLastSol();
  State invalidateLastSol();
  State invalidateLastSol(const std::vector<std::string>& names);

  ratio getLowerBound() const;
  ratio getUpperBound() const;

  bool hasSolution() const;
  std::vector<bigint> getLastSolutionFor(const std::vector<std::string>& vars) const;

  bool hasCore() const;
  std::vector<std::string> getLastCore() const;

  void printOrigSol() const;
  void printFormula();

  std::vector<std::pair<bigint, bigint>> propagate(const std::vector<std::string>& varnames);
};
std::ostream& operator<<(std::ostream& o, const ILP& x);

}  // namespace xct
