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
    o << "[" << 0 << "," << x.getUpperBound() - x.getLowerBound() << "]";
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const IntTerm& x) { return o << x.c << (x.negated ? " ~" : " ") << *x.v; }
std::ostream& operator<<(std::ostream& o, const IntConstraint& x) {
  if (x.getUB().has_value()) o << x.getUB().value() << " >= ";
  std::vector<std::string> terms;
  terms.reserve(x.getLhs().size());
  for (const IntTerm& t : x.getLhs()) {
    std::stringstream ss;
    ss << t;
    terms.push_back(ss.str());
  }
  std::sort(terms.begin(), terms.end());
  for (const std::string& s : terms) o << s << " ";
  if (x.getLB().has_value()) o << ">= " << x.getLB().value();
  return o;
}

IntVar::IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub, int loglim)
    : name(n), lowerBound(lb), upperBound(ub), logEncoding(getRange() > loglim) {
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
        // TODO: last variable may have a smaller coefficient if the range is not a nice power of two - 1
        solver.addConstraint(ConstrSimpleArb({lhs}, -range), Origin::FORMULA);
      } else {  // binary order constraints
        for (Var var = oldvars + 1; var < oldvars + newvars; ++var) {
          solver.addConstraint(ConstrSimple32({{1, var}, {-1, var + 1}}, 0), Origin::FORMULA);
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

ILP::ILP(bool keepIn) : solver(global), obj({}, {}, {}, 0), keepInput(keepIn) {
  global.stats.startTime = std::chrono::steady_clock::now();
}

IntVar* ILP::addVar(const std::string& name, const bigint& lowerbound, const bigint& upperbound, bool nameAsId) {
  assert(!getVarFor(name));
  if (lowerbound > upperbound) {
    std::stringstream ss;
    ss << "Lower bound " << lowerbound << " of " << name << " exceeds upper bound " << upperbound;
    throw std::invalid_argument(ss.str());
  }
  vars.push_back(
      std::make_unique<IntVar>(name, solver, nameAsId, lowerbound, upperbound, global.options.ilpEncoding.get()));
  IntVar* iv = vars.back().get();
  name2var.insert({name, iv});
  for (Var v : iv->encodingVars()) {
    var2var.insert({v, iv});
  }
  return iv;
}

IntVar* ILP::getVarFor(const std::string& name) const {
  if (auto it = name2var.find(name); it != name2var.end()) return it->second;
  return nullptr;
}

std::vector<IntVar*> ILP::getVariables() const {
  return aux::comprehension(name2var, [](auto pair) { return pair.second; });
}

std::pair<bigint, bigint> ILP::getBounds(IntVar* iv) const { return {iv->getLowerBound(), iv->getUpperBound()}; }

void ILP::setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const std::vector<bool>& negated, const bigint& mult, const bigint& offset) {
  if (coefs.size() != vars.size() || (!negated.empty() && negated.size() != vars.size()))
    throw std::invalid_argument("Coefficient, variable, or negated lists differ in size.");
  if (mult == 0) throw std::invalid_argument("Objective multiplier should not be zero.");
  if (initialized()) throw std::invalid_argument("Objective already set.");
  obj = IntConstraint(coefs, vars, negated, -offset);
  objmult = mult;
}

void ILP::setAssumptions(const std::vector<bigint>& vals, const std::vector<IntVar*>& vars) {
  if (vals.size() != vars.size()) throw std::invalid_argument("Value and variable lists differ in size.");

  assumptions.clear();
  for (int i = 0; i < (int)vars.size(); ++i) {
    IntVar* iv = vars[i];
    assert(iv);
    assert(vals[i] <= iv->getUpperBound());
    bigint val = vals[i] - iv->getLowerBound();
    if (val < 0) throw std::invalid_argument("Assumed value for " + iv->getName() + " exceeds variable bounds.");
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

void ILP::addConstraint(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                        const std::vector<bool>& negated, const std::optional<bigint>& lb,
                        const std::optional<bigint>& ub) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() > 1e9) throw std::invalid_argument("Constraint has more than 1e9 terms.");

  IntConstraint ic(coefs, vars, negated, lb, ub);
  if (keepInput) constraints.push_back(ic);
  if (ic.getLB().has_value()) {
    CeArb input = global.cePools.takeArb();
    ic.toConstrExp(input, true);
    solver.addConstraint(input, Origin::FORMULA);
  }
  if (ic.getUB().has_value()) {
    CeArb input = global.cePools.takeArb();
    ic.toConstrExp(input, false);
    solver.addConstraint(input, Origin::FORMULA);
  }
}

// head <=> rhs -- head iff rhs
void ILP::addReification(IntVar* head, const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                         const std::vector<bool>& negated, const bigint& lb) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw std::invalid_argument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw std::invalid_argument("Head of reification is not Boolean.");

  IntConstraint ic(coefs, vars, negated, lb);
  if (keepInput) reifications.push_back({head, ic});
  CeArb leq = global.cePools.takeArb();
  ic.toConstrExp(leq, true);
  leq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, global.stats);
  CeArb geq = global.cePools.takeArb();
  leq->copyTo(geq);
  Var h = head->encodingVars()[0];

  leq->addLhs(leq->degree, -h);
  solver.addConstraint(leq, Origin::FORMULA);

  geq->addRhs(-1);
  geq->invert();
  geq->addLhs(geq->degree, h);
  solver.addConstraint(geq, Origin::FORMULA);
}

// head => rhs -- head implies rhs
void ILP::addRightReification(IntVar* head, const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                              const std::vector<bool>& negated, const bigint& lb) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw std::invalid_argument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw std::invalid_argument("Head of reification is not Boolean.");

  IntConstraint ic(coefs, vars, negated, lb);
  if (keepInput) reifications.push_back({head, ic});
  CeArb leq = global.cePools.takeArb();
  ic.toConstrExp(leq, true);
  leq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, global.stats);

  Var h = head->encodingVars()[0];
  leq->addLhs(leq->degree, -h);
  solver.addConstraint(leq, Origin::FORMULA);
}

// head <= rhs -- rhs implies head
void ILP::addLeftReification(IntVar* head, const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                             const std::vector<bool>& negated, const bigint& lb) {
  if (coefs.size() != vars.size()) throw std::invalid_argument("Coefficient and variable lists differ in size.");
  if (coefs.size() >= 1e9) throw std::invalid_argument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw std::invalid_argument("Head of reification is not Boolean.");

  IntConstraint ic(coefs, vars, negated, lb);
  if (keepInput) reifications.push_back({head, ic});
  CeArb geq = global.cePools.takeArb();
  ic.toConstrExp(geq, true);
  geq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, global.stats);

  Var h = head->encodingVars()[0];
  geq->addRhs(-1);
  geq->invert();
  geq->addLhs(geq->degree, h);
  solver.addConstraint(geq, Origin::FORMULA);
}

void ILP::fix(IntVar* iv, const bigint& val) { addConstraint({1}, {iv}, {false}, val, val); }

void ILP::boundObjByLastSol() {
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");
  optim->handleNewSolution(solver.getLastSolution());
}

void ILP::invalidateLastSol() {
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(name2var.size());
  for (const auto& tup : name2var) {
    aux::appendTo(vars, tup.second->encodingVars());
  }
  solver.invalidateLastSol(vars);
}

void ILP::invalidateLastSol(const std::vector<IntVar*>& ivs) {
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(ivs.size());
  for (IntVar* iv : ivs) {
    aux::appendTo(vars, iv->encodingVars());
  }
  solver.invalidateLastSol(vars);
}

bool ILP::initialized() const { return optim != nullptr; }

void ILP::init() {
  if (initialized()) throw std::invalid_argument("Solver already initialized.");
  aux::rng::seed = global.options.randomSeed.get();

  CeArb o = global.cePools.takeArb();
  obj.toConstrExp(o, true);
  solver.init(o);
  optim = OptimizationSuper::make(o, solver, global);
}

SolveState ILP::runOnce() {  // NOTE: also throws AsynchronousInterrupt and UnsatEncounter
  if (!initialized()) throw std::invalid_argument("Solver not yet initialized.");
  return optim->optimize(assumptions);
}

SolveState ILP::runFull(double timeout) {
  if (!initialized()) throw std::invalid_argument("Solver not yet initialized.");
  global.stats.runStartTime = std::chrono::steady_clock::now();
  SolveState result = SolveState::INPROCESSED;
  while ((timeout == 0 || global.stats.getSolveTime() < timeout) &&
         (result == SolveState::INPROCESSED || result == SolveState::SAT)) {
    try {
      result = runOnce();
    } catch (const UnsatEncounter& ue) {
      return SolveState::UNSAT;
    }
  }
  return result;
}

void ILP::printFormula() { printFormula(std::cout); }

std::ostream& ILP::printFormula(std::ostream& out) {
  int nbConstraints = 0;
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    nbConstraints += isNonImplied(c.getOrigin());
  }
  out << "* #variable= " << solver.getNbVars() << " #constraint= " << nbConstraints << "\n";
  if (optim && optim->getReformObj()->nVars() > 0) {
    out << "min: ";
    optim->getReformObj()->toStreamAsOPBlhs(out, true);
    out << ";\n";
  }
  for (Lit l : solver.getUnits()) {
    out << std::pair<int, Lit>{1, l} << " >= 1 ;\n";
  }
  for (Var v = 1; v <= solver.getNbVars(); ++v) {
    if (solver.getEqualities().isCanonical(v)) continue;
    out << std::pair<int, Lit>{1, v} << std::pair<int, Lit>{-1, solver.getEqualities().getRepr(v).l} << " = 0 ;\n";
  }
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    if (isNonImplied(c.getOrigin())) {
      CeSuper ce = c.toExpanded(global.cePools);
      ce->toStreamAsOPB(out);
      out << "\n";
    }
  }
  return out;
}

std::ostream& ILP::printInput(std::ostream& out) {
  out << "OBJ " << obj << std::endl;
  std::vector<std::string> reifics;
  for (const auto& pr : reifications) {
    std::stringstream ss;
    ss << *pr.first << " <=> " << pr.second;
    reifics.push_back(ss.str());
  }
  std::sort(reifics.begin(), reifics.end());
  for (const std::string& s : reifics) out << s << std::endl;
  std::vector<std::string> constrs;
  for (const IntConstraint& ic : constraints) {
    std::stringstream ss;
    ss << ic;
    constrs.push_back(ss.str());
  }
  std::sort(constrs.begin(), constrs.end());
  for (const std::string& s : constrs) out << s << std::endl;
  return out;
}

ratio ILP::getLowerBound() const {
  if (!initialized()) throw std::invalid_argument("Objective not yet initialized.");
  return static_cast<ratio>(optim->getLowerBound());
}
ratio ILP::getUpperBound() const {
  if (!initialized()) throw std::invalid_argument("Objective not yet initialized.");
  return static_cast<ratio>(optim->getUpperBound());
}

bool ILP::hasSolution() const {
  if (!initialized()) return false;
  assert((optim->solutionsFound > 0) == solver.foundSolution());
  return optim->solutionsFound > 0;
}

bigint ILP::getLastSolutionFor(IntVar* iv) const {
  if (!hasSolution()) throw std::invalid_argument("No solution to return.");
  return iv->getValue(solver.getLastSolution());
}

std::vector<bigint> ILP::getLastSolutionFor(const std::vector<IntVar*>& vars) const {
  if (!hasSolution()) throw std::invalid_argument("No solution to return.");
  return aux::comprehension(vars, [&](IntVar* iv) { return getLastSolutionFor(iv); });
}

bool ILP::hasCore() const { return solver.assumptionsClashWithUnits() || solver.lastCore; }

std::unordered_set<IntVar*> ILP::getLastCore() {
  if (!hasCore()) throw std::invalid_argument("No unsat core to return.");

  std::unordered_set<IntVar*> core;
  if (solver.assumptionsClashWithUnits()) {
    for (Lit l : assumptions) {
      if (isUnit(solver.getLevel(), -l)) core.insert(var2var.at(toVar(l)));
    }
  } else {
    std::unordered_set<Lit> assumps(assumptions.begin(), assumptions.end());
    CeSuper clone = solver.lastCore->clone(global.cePools);
    clone->weaken([assumps](Lit l) { return !assumps.count(-l); });
    clone->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    clone->simplifyToClause();
    for (Var v : clone->vars) {
      core.insert(var2var.at(v));
    }
  }
  assert(!core.empty());
  return core;
}

void ILP::printOrigSol() const {
  if (!hasSolution()) throw std::invalid_argument("No solution to return.");
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->getValue(solver.getLastSolution());
    if (val != 0) {
      std::cout << iv->getName() << " " << val << "\n";
    }
  }
}

// NOTE: also throws AsynchronousInterrupt
std::vector<std::pair<bigint, bigint>> ILP::propagate(const std::vector<IntVar*>& ivs) {
  global.options.boundUpper.set(false);
  global.options.pureLits.set(false);
  global.options.domBreakLim.set(0);
  SolveState result = SolveState::INPROCESSED;
  while (result == SolveState::INPROCESSED) {
    result = runOnce();
  }
  if (result == SolveState::INCONSISTENT) {
    throw std::invalid_argument("Propagation cannot be done with inconsistent assumptions.");
  }
  assert(result == SolveState::SAT);

  Ce32 invalidator = global.cePools.take32();
  invalidator->addRhs(1);
  for (IntVar* iv : ivs) {
    for (Var v : iv->encodingVars()) {
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
    solver.addConstraint(invalidator, Origin::INVALIDATOR);
    result = SolveState::INPROCESSED;
    while (result == SolveState::INPROCESSED) {
      result = runOnce();
    }
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
  solver.addUnitConstraint(marker, Origin::INVALIDATOR);
  assert(invalidator->isClause());
  invalidator->weaken(marker);
  invalidator->removeZeroes();
  assert(invalidator->getDegree() == 0);

  std::vector<std::pair<bigint, bigint>> consequences;
  consequences.reserve(ivs.size());
  for (IntVar* iv : ivs) {
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
  solver.addConstraint(invalidator, Origin::INVALIDATOR);

  return consequences;
}

}  // namespace xct
