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

#include "ILP.hpp"
#include <stdexcept>
#include "Optimization.hpp"

namespace xct {

std::ostream& operator<<(std::ostream& o, const IntVar& x) {
  o << x.getName();
  if (!x.isBoolean()) {
    o << "[" << x.getLowerBound() << "," << x.getUpperBound() << "]";
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const IntTerm& x) { return o << x.c << (x.negated ? "~x" : "x") << *x.v; }
std::ostream& operator<<(std::ostream& o, const IntConstraint& x) {
  if (x.getUB().has_value()) o << x.getUB().value() << " >= ";
  for (const IntTerm& t : x.getLhs()) o << t << " ";
  if (x.getLB().has_value()) o << " >= " << x.getLB().value();
  return o;
}

IntVar::IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub)
    : name(n), lowerBound(lb), upperBound(ub), logEncoding(getRange() > options.ilpEncoding.get()) {
  assert(lb <= ub);
  assert(!nameAsId || isBoolean());

  if (nameAsId) {
    Var next = std::stoi(getName());
    solver.setNbVars(next, true);
    encoding.emplace_back(next);
  } else {
    const bigint range = getRange();
    if (range != 0) {
      int newvars = logEncoding ? aux::msb(range) + 1 : static_cast<int>(range);
      int oldvars = solver.getNbVars();
      solver.setNbVars(oldvars + newvars, true);
      for (Var var = oldvars + 1; var <= oldvars + newvars; ++var) {
        encoding.emplace_back(var);
      }
      if (logEncoding) {  // upper bound constraint
        std::vector<Term<bigint>> lhs;
        lhs.reserve(encoding.size());
        bigint base = -1;
        for (const Var v : encoding) {
          lhs.emplace_back(base, v);
          base *= 2;
        }
        solver.addConstraintUnchecked(ConstrSimpleArb({lhs}, -range), Origin::FORMULA);
      } else {  // binary order constraints
        for (Var var = oldvars + 1; var < oldvars + newvars; ++var) {
          solver.addConstraintUnchecked(ConstrSimple32({{1, var}, {-1, var + 1}}, 0), Origin::FORMULA);
        }
      }
    }
  }
}

bigint IntVar::getValue(const std::vector<Lit>& sol) const {
  bigint val = getLowerBound();
  if (usesLogEncoding()) {
    bigint base = 1;
    for (Var v : encodingVars()) {
      assert(v < (int)sol.size());
      assert(toVar(sol[v]) == v);
      if (sol[v] > 0) val += base;
      base *= 2;
    }
  } else {
    int sum = 0;
    for (Var v : encodingVars()) {
      assert(v < (int)sol.size());
      assert(toVar(sol[v]) == v);
      sum += sol[v] > 0;
    }
    val += sum;
  }
  return val;
}

IntConstraint::IntConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                             const std::vector<bool>& negated, const std::optional<bigint>& lb,
                             const std::optional<bigint>& ub)
    : lowerBound(lb), upperBound(ub) {
  assert(coefs.size() == vars.size());
  assert(negated.empty() || negated.size() == coefs.size());
  lhs.reserve(coefs.size());
  for (int i = 0; i < (int)coefs.size(); ++i) {
    lhs.emplace_back(coefs[i], vars[i], !negated.empty() && negated[i]);
  }
  normalize();
}

void IntConstraint::toConstrExp(CeArb& input, bool useLowerBound) const {
  if (useLowerBound) {
    assert(lowerBound.has_value());
    input->addRhs(lowerBound.value());
  } else {
    assert(upperBound.has_value());
    input->addRhs(upperBound.value());
  }
  for (const IntTerm& t : lhs) {
    assert(!t.negated);
    if (t.v->getRange() == 0) continue;
    assert(!t.v->encodingVars().empty());
    if (t.v->usesLogEncoding()) {
      bigint base = 1;
      for (const Var v : t.v->encodingVars()) {
        input->addLhs(base * t.c, v);
        base *= 2;
      }
    } else {
      for (const Var v : t.v->encodingVars()) {
        input->addLhs(t.c, v);
      }
    }
  }
  if (!useLowerBound) input->invert();
}

// Normalization removes remove negated terms and turns the constraint in GTE or EQ
void IntConstraint::normalize() {
  for (IntTerm& t : lhs) {
    if (t.negated) {
      assert(t.v->isBoolean());
      t.c = -t.c;
      if (lowerBound.has_value()) lowerBound = lowerBound.value() + t.c;
      if (upperBound.has_value()) upperBound = upperBound.value() + t.c;
      t.negated = false;
    } else if (t.v->getLowerBound() != 0) {
      bigint adjustment = -t.c * t.v->getLowerBound();
      if (lowerBound.has_value()) lowerBound = lowerBound.value() + adjustment;
      if (upperBound.has_value()) upperBound = upperBound.value() + adjustment;
    }
  }
}

ILP::ILP() : solver(*this), obj({}, {}, {}, 0) {}

IntVar* ILP::getVarFor(const std::string& name, bool nameAsId, const bigint& lowerbound, const bigint& upperbound) {
  if (auto it = name2var.find(name); it != name2var.end()) return it->second;
  if (lowerbound > upperbound) {
    std::stringstream ss;
    ss << "Lower bound " << lowerbound << " of " << name << " exceeds upper bound " << upperbound;
    throw std::invalid_argument(ss.str());
  }
  vars.push_back(std::make_unique<IntVar>(name, solver, nameAsId, lowerbound, upperbound));
  IntVar* iv = vars.back().get();
  name2var.insert({name, iv});
  for (Var v : iv->encodingVars()) {
    var2var.insert({v, iv});
  }
  return iv;
}

bool ILP::hasVarFor(const std::string& name) const { return name2var.count(name); }

std::vector<std::string> ILP::getVariables() const {
  std::vector<std::string> keys(name2var.size());
  transform(name2var.begin(), name2var.end(), keys.begin(), [](auto pair) { return pair.first; });
  return keys;
}

std::pair<bigint, bigint> ILP::getBounds(const std::string& name) const {
  if (!hasVarFor(name)) throw std::invalid_argument("No variable " + name + " found.");
  IntVar* iv = name2var.at(name);
  return {iv->getLowerBound(), iv->getUpperBound()};
}

void ILP::setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const std::vector<bool>& negated, const bigint& mult, const bigint& offset) {
  if (coefs.size() != vars.size() || (!negated.empty() && negated.size() != vars.size()))
    throw std::invalid_argument("Coefficient, variable, or negated lists differ in size.");
  if (mult == 0) throw std::invalid_argument("Objective multiplier should not be zero.");
  if (optim) throw std::invalid_argument("Objective already set.");
  obj = IntConstraint(coefs, vars, negated, -offset);
  objmult = mult;
}

void ILP::setAssumptions(const std::vector<bigint>& vals, const std::vector<IntVar*>& vars) {
  if (unsatDetected) throw UnsatState();
  if (vals.size() != vars.size()) throw std::invalid_argument("Value and variable lists differ in size.");

  assumptions.clear();
  for (int i = 0; i < (int)vars.size(); ++i) {
    IntVar* iv = vars[i];
    assert(vals[i] <= iv->getUpperBound());
    bigint val = vals[i] - iv->getLowerBound();
    assert(val >= 0);
    if (iv->usesLogEncoding()) {
      for (const Var v : iv->encodingVars()) {
        assumptions.push_back(val % 2 == 0 ? -v : v);
        val /= 2;
      }
      assert(val == 0);
    } else {
      assert(val <= iv->encodingVars().size());
      int val_int = static_cast<int>(val);
      if (val_int > 0) {
        assumptions.push_back(iv->encodingVars()[val_int - 1]);
      }
      if (val_int < (int)iv->encodingVars().size()) {
        assumptions.push_back(-iv->encodingVars()[val_int]);
      }
    }
  }
}

State ILP::addConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                         const std::vector<bool>& negated, const std::optional<bigint>& lb,
                         const std::optional<bigint>& ub) {
  if (unsatDetected) throw UnsatState();
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() > 1e9) throw std::invalid_argument("Constraint has more than 1e9 terms.");

  IntConstraint ic(coefs, vars, negated, lb, ub);
  if (ic.getLB().has_value()) {
    CeArb input = cePools.takeArb();
    ic.toConstrExp(input, true);
    if (solver.addConstraint(input, Origin::FORMULA).second == ID_Unsat) {
      unsatDetected = true;
      return State::UNSAT;
    }
  }
  if (ic.getUB().has_value()) {
    CeArb input = cePools.takeArb();
    ic.toConstrExp(input, false);
    if (solver.addConstraint(input, Origin::FORMULA).second == ID_Unsat) {
      unsatDetected = true;
      return State::UNSAT;
    }
  }
  return State::SUCCESS;
}

State ILP::addReification(IntVar* head, const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                          const bigint& lb) {
  if (unsatDetected) throw UnsatState();
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw std::invalid_argument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw std::invalid_argument("Head of reification is not Boolean.");

  IntConstraint ic(coefs, vars, {}, lb);
  CeArb leq = cePools.takeArb();
  ic.toConstrExp(leq, true);
  leq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true);
  CeArb geq = cePools.takeArb();
  leq->copyTo(geq);
  Var h = head->encodingVars()[0];

  leq->addLhs(leq->degree, -h);
  if (solver.addConstraint(leq, Origin::FORMULA).second == ID_Unsat) {
    unsatDetected = true;
    return State::UNSAT;
  }

  geq->addRhs(-1);
  geq->invert();
  geq->addLhs(geq->degree, h);
  if (solver.addConstraint(geq, Origin::FORMULA).second == ID_Unsat) {
    unsatDetected = true;
    return State::UNSAT;
  }

  return State::SUCCESS;
}

State ILP::boundObjByLastSol() {
  if (unsatDetected) throw UnsatState();
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");
  State result = optim->handleNewSolution(solver.getLastSolution());
  assert(result != State::FAIL);
  unsatDetected = result == State::UNSAT;
  return result;
}

State ILP::invalidateLastSol() {
  if (unsatDetected) throw UnsatState();
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(name2var.size());
  for (const auto& tup : name2var) {
    aux::appendTo(vars, tup.second->encodingVars());
  }
  std::pair<ID, ID> ids = solver.invalidateLastSol(vars);
  unsatDetected = ids.second == ID_Unsat;
  return unsatDetected ? State::UNSAT : State::SUCCESS;
}

State ILP::invalidateLastSol(const std::vector<std::string>& names) {
  if (unsatDetected) throw UnsatState();
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(names.size());
  for (const std::string& name : names) {
    aux::appendTo(vars, name2var[name]->encodingVars());
  }
  std::pair<ID, ID> ids = solver.invalidateLastSol(vars);
  assert(ids.second != ID_Undef);
  unsatDetected = ids.second == ID_Unsat;
  return unsatDetected ? State::UNSAT : State::SUCCESS;
}

void ILP::init(bool boundObjective, bool addNonImplieds) {
  if (unsatDetected) throw UnsatState();
  if (optim) throw std::invalid_argument("ILP already initialized.");

  // TODO: below should be set at option parsing time?
  if (!boundObjective) {
    options.boundUpper.parse("0");
  }
  if (!addNonImplieds) {
    options.pureLits.parse("0");
    options.domBreakLim.parse("0");
  }
  asynch_interrupt = false;
  aux::rng::seed = options.randomSeed.get();

  CeArb o = cePools.takeArb();
  obj.toConstrExp(o, true);
  solver.init(o);
  optim = OptimizationSuper::make(o, solver);
}

SolveState ILP::run() {  // NOTE: also throws AsynchronousInterrupt
  if (unsatDetected) throw UnsatState();
  SolveState result = optim->optimize(assumptions);
  unsatDetected = result == SolveState::UNSAT;
  return result;
}

SolveState ILP::runFull() {  // NOTE: also throws AsynchronousInterrupt
  if (unsatDetected) throw UnsatState();
  SolveState result = SolveState::INPROCESSED;
  while (result == SolveState::INPROCESSED) {
    result = optim->optimize(assumptions);
  }
  unsatDetected = result == SolveState::UNSAT;
  return result;
}

void ILP::printFormula() {
  int nbConstraints = 0;
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    nbConstraints += isNonImplied(c.getOrigin());
  }
  std::cout << "* #variable= " << solver.getNbVars() << " #constraint= " << nbConstraints << "\n";
  std::cout << "min: ";
  optim->getReformObj()->toStreamAsOPBlhs(std::cout);
  std::cout << "; \n";
  for (Lit l : solver.getUnits()) {
    std::cout << std::pair<int, Lit>{1, l} << " >= 1 ;\n";
  }
  for (Var v = 1; v <= solver.getNbVars(); ++v) {
    if (solver.getEqualities().isCanonical(v)) continue;
    std::cout << std::pair<int, Lit>{1, v} << std::pair<int, Lit>{-1, solver.getEqualities().getRepr(v).l}
              << " = 0 ;\n";
  }
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    if (isNonImplied(c.getOrigin())) {
      CeSuper ce = c.toExpanded(cePools);
      ce->toStreamAsOPB(std::cout);
      std::cout << "\n";
    }
  }
}

ratio ILP::getLowerBound() const {
  return optim ? static_cast<ratio>(optim->getLowerBound()) / objmult : static_cast<ratio>(0);
}
ratio ILP::getUpperBound() const {
  return optim ? static_cast<ratio>(optim->getUpperBound()) / objmult : static_cast<ratio>(0);
}

bool ILP::hasSolution() const {
  bool result = optim && optim->solutionsFound > 0;
  assert(result == solver.foundSolution());
  return result;
}

std::vector<bigint> ILP::getLastSolutionFor(const std::vector<std::string>& vars) const {
  if (!hasSolution()) throw std::invalid_argument("No solution to return.");

  std::vector<bigint> result;
  result.reserve(vars.size());
  for (const std::string& var : vars) {
    if (!name2var.count(var)) throw std::invalid_argument("No known variable " + var + ".");
    result.push_back(name2var.at(var)->getValue(solver.getLastSolution()));
  }
  return result;
}

bool ILP::hasCore() const { return solver.assumptionsClashWithUnits() || solver.lastCore; }

std::vector<std::string> ILP::getLastCore() const {
  if (!hasCore()) throw std::invalid_argument("No unsat core to return.");

  std::unordered_set<IntVar*> core;
  if (solver.assumptionsClashWithUnits()) {
    for (Lit l : assumptions) {
      if (isUnit(solver.getLevel(), -l)) core.insert(var2var.at(toVar(l)));
    }
  } else {
    CeSuper clone = solver.lastCore->clone(cePools);
    clone->simplifyToClause();
    for (Var v : clone->vars) {
      core.insert(var2var.at(v));
    }
  }
  assert(!core.empty());
  std::vector<std::string> result;
  result.reserve(core.size());
  for (IntVar* iv : core) {
    result.push_back(iv->getName());
  }
  return result;
}

void ILP::printOrigSol() const {
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->getValue(solver.getLastSolution());
    if (val != 0) {
      std::cout << iv->getName() << " " << val << "\n";
    }
  }
}

// NOTE: also throws AsynchronousInterrupt
std::vector<std::pair<bigint, bigint>> ILP::propagate(const std::vector<std::string>& varnames) {
  SolveState result = runFull();
  if (unsatDetected) throw UnsatState();
  if (result == SolveState::INCONSISTENT) return {};
  assert(result == SolveState::SAT);

  Ce32 invalidator = cePools.take32();
  invalidator->addRhs(1);
  for (const std::string& vn : varnames) {
    for (Var v : name2var[vn]->encodingVars()) {
      invalidator->addLhs(1, -solver.getLastSolution()[v]);
    }
  }
  for (Lit l : assumptions) {
    invalidator->addLhs(-1, -l);  // no need to add assumptions to invalidator
  }
  Var marker = solver.getNbVars() + 1;
  solver.setNbVars(marker, true);
  assumptions.push_back(-marker);
  invalidator->addLhs(1, marker);
  invalidator->removeZeroes();
  assert(invalidator->isClause());

  while (true) {
    solver.addConstraintUnchecked(invalidator, Origin::INVALIDATOR);
    result = runFull();
    if (result != SolveState::SAT) break;
    for (Var v : invalidator->getVars()) {
      Lit invallit = invalidator->getLit(v);
      if (solver.getLastSolution()[v] == invallit) {  // solution matches invalidator
        invalidator->addLhs(-1, invallit);
      }
    }
    assert(!invalidator->hasNoZeroes());
    invalidator->removeZeroes();
  }
  assert(result == SolveState::INCONSISTENT);
  assumptions.pop_back();
  [[maybe_unused]] ID id = solver.addUnitConstraint(marker, Origin::INVALIDATOR);
  assert(id != ID_Unsat);
  assert(invalidator->isClause());
  invalidator->weaken(marker);
  invalidator->removeZeroes();
  assert(invalidator->getDegree() == 0);

  std::vector<std::pair<bigint, bigint>> consequences;
  consequences.reserve(varnames.size());
  for (const std::string& vn : varnames) {
    IntVar* iv = name2var[vn];
    bigint lb = iv->getLowerBound();
    bigint ub = iv->getUpperBound();
    if (iv->usesLogEncoding()) {
      bigint coef = 1;
      for (Var v : iv->encodingVars()) {
        if (invalidator->hasLit(-v)) {
          lb += coef;
        }
        if (invalidator->hasLit(v)) {
          ub -= coef;
        }
        coef *= 2;
      }
    } else {
      for (Var v : iv->encodingVars()) {
        lb += invalidator->hasLit(-v);
        ub -= invalidator->hasLit(v);
      }
    }
    consequences.push_back({lb, ub});
  }

  invalidator->invert();
  int invsize = invalidator->vars.size();
  invalidator->addRhs(invsize - invalidator->getDegree());
  assert(invalidator->getDegree() == invsize);
  for (Lit l : assumptions) {
    invalidator->addLhs(invsize, -l);
  }
  // TODO: make below a learned constraint instead of input
  solver.addConstraintUnchecked(invalidator, Origin::INVALIDATOR);

  return consequences;
}

}  // namespace xct
