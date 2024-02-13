/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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
#include "Global.hpp"
#include "Optimization.hpp"
#include "Solver.hpp"
#include "datastructures/IntSet.hpp"
#include "typedefs.hpp"

namespace xct {

enum class Encoding { ORDER, LOG, ONEHOT };
Encoding opt2enc(const std::string& opt);

struct IntVar {
  explicit IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub, Encoding e);

  [[nodiscard]] const std::string& getName() const { return name; }
  [[nodiscard]] const bigint& getUpperBound() const { return upperBound; }
  [[nodiscard]] const bigint& getLowerBound() const { return lowerBound; }

  [[nodiscard]] bigint getRange() const { return upperBound - lowerBound; }  // TODO: Boolean range is 1?
  [[nodiscard]] bool isBoolean() const { return lowerBound == 0 && upperBound == 1; }

  [[nodiscard]] Encoding getEncoding() const { return encoding; }
  [[nodiscard]] const std::vector<Var>& getEncodingVars() const { return encodingVars; }
  [[nodiscard]] bigint getValue(const std::vector<Lit>& sol) const;

  [[nodiscard]] const std::vector<Var>& getPropVars(Solver& solver);
  [[nodiscatd]] Var getPropVar() const;

 private:
  const std::string name;
  const bigint lowerBound;
  const bigint upperBound;

  const Encoding encoding;
  std::vector<Var> encodingVars;

  std::vector<Var> propVars;
  Var propVar;
};
std::ostream& operator<<(std::ostream& o, const IntVar& x);
std::ostream& operator<<(std::ostream& o, IntVar* x);

struct IntTerm {
  bigint c;
  IntVar* v;
  bool negated;

  IntTerm(const bigint& val, IntVar* var, bool neg) : c(val), v(var), negated(neg) {}
};
std::ostream& operator<<(std::ostream& o, const IntTerm& x);

class ILP;

class IntConstraint {
  friend class ILP;
  std::vector<IntTerm> lhs;
  std::optional<bigint> lowerBound;
  std::optional<bigint> upperBound;

  void normalize();

 public:
  IntConstraint();
  IntConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars, const std::vector<bool>& negated,
                const std::optional<bigint>& lb = std::nullopt, const std::optional<bigint>& ub = std::nullopt);

  const std::vector<IntTerm>& getLhs() const;
  const std::optional<bigint>& getLB() const;
  const std::optional<bigint>& getUB() const;
  const bigint getRange() const;
  int64_t size() const;

  void toConstrExp(CeArb&, bool useLowerBound) const;
};
std::ostream& operator<<(std::ostream& o, const IntConstraint& x);

struct OptRes {
  SolveState state;
  bigint optval;
  std::vector<IntVar*> core;
};

class ILP {
 public:
  Global global;

 private:
  Solver solver;
  Optim optim;

  std::vector<std::unique_ptr<IntVar>> vars;
  IntConstraint obj;  // NOTE: we could erase this, but then we would not store the untransformed input objective
  unordered_map<std::string, IntVar*> name2var;
  unordered_map<Var, IntVar*> var2var;

  int maxSatVars = -1;

  xct::IntSet assumptions;

  // only for printing purposes:
  const bool keepInput;
  std::vector<IntConstraint> constraints;
  std::vector<std::pair<IntVar*, IntConstraint>> reifications;

  IntVar* addFlag();
  Var fixObjective(const IntConstraint& ico, const bigint& opt);

 public:
  OptRes toOptimum(IntConstraint& objective, bool keepstate, double timeout);

  ILP(const Options& opts, bool keepIn = false);

  const Solver& getSolver() const;
  Solver& getSolver();
  const Optim& getOptim() const;
  void setMaxSatVars();
  int getMaxSatVars() const;

  IntVar* addVar(const std::string& name, const bigint& lowerbound, const bigint& upperbound, Encoding encoding,
                 bool nameAsId = false);
  IntVar* getVarFor(const std::string& name) const;  // returns nullptr if it does not exist
  std::vector<IntVar*> getVariables() const;
  std::pair<bigint, bigint> getBounds(IntVar* iv) const;

  void setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                    const std::vector<bool>& negated, const bigint& offset = 0);
  IntConstraint& getObjective();
  const IntConstraint& getObjective() const;
  void setAssumption(const IntVar* iv, const std::vector<bigint>& vals);
  void setAssumption(const IntVar* iv, bool val);
  bool hasAssumption(const IntVar* iv) const;
  std::vector<bigint> getAssumption(const IntVar* iv) const;
  void clearAssumptions();
  void clearAssumption(const IntVar* iv);

  void setSolutionHints(const std::vector<IntVar*>& ivs, const std::vector<bigint>& vals);
  void clearSolutionHints(const std::vector<IntVar*>& ivs);

  void runFromCmdLine();

  void addConstraint(const IntConstraint& ic);
  void addReification(IntVar* head, const IntConstraint& ic);
  void addRightReification(IntVar* head, const IntConstraint& ic);
  void addLeftReification(IntVar* head, const IntConstraint& ic);
  void fix(IntVar* iv, const bigint& val);
  void invalidateLastSol();
  void invalidateLastSol(const std::vector<IntVar*>& ivs, Var flag = 0);

  ratio getLowerBound() const;
  ratio getUpperBound() const;

  bigint getLastSolutionFor(IntVar* iv) const;
  std::vector<bigint> getLastSolutionFor(const std::vector<IntVar*>& vars) const;

  std::optional<std::vector<IntVar*>> getLastCore();

  void printOrigSol() const;
  void printFormula();
  std::ostream& printFormula(std::ostream& out);
  std::ostream& printInput(std::ostream& out) const;
  std::ostream& printVars(std::ostream& out) const;
  long long getNbVars() const;
  long long getNbConstraints() const;
  bigint getSolSpaceSize() const;  // in bits

  std::pair<SolveState, Ce32> getSolIntersection(const std::vector<IntVar*>& ivs, bool keepstate, double timeout = 0);
  const std::vector<std::pair<bigint, bigint>> propagate(const std::vector<IntVar*>& ivs, bool keepstate,
                                                         double timeout = 0);
  const std::vector<std::vector<bigint>> pruneDomains(const std::vector<IntVar*>& ivs, bool keepstate,
                                                      double timeout = 0);
  std::pair<SolveState, int64_t> count(const std::vector<IntVar*>& ivs, bool keepstate, double timeout = 0);
};
std::ostream& operator<<(std::ostream& o, const ILP& x);

}  // namespace xct
