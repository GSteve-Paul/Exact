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

class ILP {
  Solver solver;
  Optim optim;

  std::vector<std::unique_ptr<IntVar>> vars;
  std::vector<IntConstraint> constrs;
  IntConstraint obj;
  bigint objmult = 0;
  std::unordered_map<std::string, IntVar*> name2var;

  int maxSatVars = -1;

 public:
  ILP();

  const IntConstraint& getObjective() const { return obj; }
  const std::vector<IntConstraint>& getConstraints() const { return constrs; }
  Solver& getSolver() { return solver; }
  Optim getOptimization() { return optim; }
  void setMaxSatVars() { maxSatVars = solver.getNbVars(); }
  int getMaxSatVars() const { return maxSatVars; }

  IntVar* getVarFor(const std::string& name, bool nameAsId = true, const bigint& lowerbound = 0,
                    const bigint& upperbound = 1);
  bool hasVarFor(const std::string& name) const;

  void setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                    const std::vector<bool>& negated, const bigint& mult = 1, const bigint& offset = 0);
  bool hasObjective() const { return objmult != 0; }

  void init();
  SolveState run();

  State addConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                      const std::vector<bool>& negated, const std::optional<bigint>& lb = std::nullopt,
                      const std::optional<bigint>& ub = std::nullopt);

  void printOrigSol(const std::vector<Lit>& sol);

  bool hasUpperBound() const;
  ratio getUpperBound() const;

  bool hasSolution() const;
};
std::ostream& operator<<(std::ostream& o, const ILP& x);

}  // namespace xct
