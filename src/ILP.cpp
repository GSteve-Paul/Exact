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
  return o << x.getName() << "[" << x.getLowerBound() << "," << x.getUpperBound() << "]";
}
std::ostream& operator<<(std::ostream& o, const IntTerm& x) {
  return o << (x.c < 0 ? "" : "+") << x.c << (x.negated ? "*~" : "*") << *x.v;
}
void lhs2str(std::ostream& o, const IntConstraint& x) {
  std::vector<std::string> terms;
  terms.reserve(x.getLhs().size());
  for (const IntTerm& t : x.getLhs()) {
    terms.push_back(aux::str(t));
  }
  std::sort(terms.begin(), terms.end());
  for (const std::string& s : terms) o << s << " ";
}
std::ostream& operator<<(std::ostream& o, const IntConstraint& x) {
  if (x.getUB().has_value()) o << x.getUB().value() << " >= ";
  lhs2str(o, x);
  if (x.getLB().has_value()) o << ">= " << x.getLB().value();
  return o;
}

Encoding opt2enc(const std::string& opt) {
  return opt == "order" ? Encoding::ORDER : opt == ("log") ? Encoding::LOG : Encoding::ONEHOT;
}
IntVar::IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub, Encoding e)
    : name(n), lowerBound(lb), upperBound(ub), encoding(getRange() <= 1 ? Encoding::ORDER : e) {
  assert(lb <= ub);

  if (nameAsId) {
    assert(isBoolean());
    Var next = std::stoi(getName());
    solver.setNbVars(next, true);
    encodingVars.emplace_back(next);
  } else {
    const bigint range = getRange();
    assert(range != 0 || encoding == Encoding::ORDER);
    int newvars = range == 0 ? 1
                             : (encoding == Encoding::LOG
                                    ? aux::msb(range) + 1
                                    : static_cast<int>(range) + static_cast<int>(encoding == Encoding::ONEHOT));
    int oldvars = solver.getNbVars();
    solver.setNbVars(oldvars + newvars, true);
    for (Var var = oldvars + 1; var <= oldvars + newvars; ++var) {
      encodingVars.emplace_back(var);
    }
    if (encoding == Encoding::LOG) {  // upper bound constraint
      std::vector<Term<bigint>> lhs;
      lhs.reserve(encodingVars.size());
      bigint base = -1;
      for (const Var v : encodingVars) {
        lhs.emplace_back(base, v);
        base *= 2;
      }
      // NOTE: last variable could have a smaller coefficient if the range is not a nice power of two - 1
      // This would actually increase the number of solutions to the constraint. It would also not guarantee that each
      // value for an integer variable had a unique Boolean representation. Bad idea probably.
      solver.addConstraint(ConstrSimpleArb({lhs}, -range), Origin::FORMULA);
    } else if (encoding == Encoding::ORDER) {
      if (range == 0) {
        solver.addUnitConstraint(-newvars, Origin::FORMULA);
        // TODO: project this variable away instead of adding a unit variable
      } else {
        for (Var var = oldvars + 1; var < oldvars + newvars; ++var) {
          solver.addConstraint(ConstrSimple32({{1, var}, {-1, var + 1}}, 0), Origin::FORMULA);
        }
      }
    } else {
      assert(encoding == Encoding::ONEHOT);
      std::vector<Term<int>> lhs1;
      lhs1.reserve(encodingVars.size());
      std::vector<Term<int>> lhs2;
      lhs2.reserve(encodingVars.size());
      for (int var = oldvars + 1; var <= oldvars + newvars; ++var) {
        lhs1.emplace_back(1, var);
        lhs2.emplace_back(-1, var);
      }
      solver.addConstraint(ConstrSimple32(lhs1, 1), Origin::FORMULA);
      solver.addConstraint(ConstrSimple32(lhs2, -1), Origin::FORMULA);
    }
  }
}

bigint IntVar::getValue(const std::vector<Lit>& sol) const {
  bigint val = getLowerBound();
  if (encoding == Encoding::LOG) {
    bigint base = 1;
    for (Var v : getEncodingVars()) {
      assert(v < (int)sol.size());
      assert(toVar(sol[v]) == v);
      if (sol[v] > 0) val += base;
      base *= 2;
    }
  } else if (encoding == Encoding::ORDER) {
    int sum = 0;
    for (Var v : getEncodingVars()) {
      assert(v < (int)sol.size());
      assert(toVar(sol[v]) == v);
      sum += sol[v] > 0;
    }
    val += sum;
  } else {
    assert(encoding == Encoding::ONEHOT);
    int ith = 0;
    for (Var v : getEncodingVars()) {
      assert(v < (int)sol.size());
      assert(toVar(sol[v]) == v);
      if (sol[v] > 0) {
        val += ith;
        break;
      }
      ++ith;
    }
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
    if (t.v->getRange() == 0) continue; // variables will have value 0 anyway
    assert(!t.v->getEncodingVars().empty());
    if (t.v->getEncoding() == Encoding::LOG) {
      bigint base = 1;
      for (const Var v : t.v->getEncodingVars()) {
        input->addLhs(base * t.c, v);
        base *= 2;
      }
    } else if (t.v->getEncoding() == Encoding::ORDER) {
      for (const Var v : t.v->getEncodingVars()) {
        input->addLhs(t.c, v);
      }
    } else {
      assert(t.v->getEncoding() == Encoding::ONEHOT);
      int ith = 0;
      for (const Var v : t.v->getEncodingVars()) {
        input->addLhs(ith * t.c, v);
        ++ith;
      }
    }
  }
  if (!useLowerBound) input->invert();
}

// Normalization removes negated terms and turns the constraint in GTE or EQ
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

IntVar* ILP::addVar(const std::string& name, const bigint& lowerbound, const bigint& upperbound,
                    const std::string& encoding, bool nameAsId) {
  assert(!getVarFor(name));
  if (upperbound < lowerbound) {
    std::stringstream ss;
    ss << "Upper bound " << upperbound << " of " << name << " is smaller than lower bound " << lowerbound;
    throw std::invalid_argument(ss.str());
  }
  vars.push_back(std::make_unique<IntVar>(name, solver, nameAsId, lowerbound, upperbound,
                                          opt2enc(encoding == "" ? solver.getOptions().ilpEncoding.get() : encoding)));
  IntVar* iv = vars.back().get();
  name2var.insert({name, iv});
  for (Var v : iv->getEncodingVars()) {
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
                       const std::vector<bool>& negated, const bigint& offset) {
  if (coefs.size() != vars.size() || (!negated.empty() && negated.size() != vars.size()))
    throw std::invalid_argument("Coefficient, variable, or negated lists differ in size.");
  if (initialized()) throw std::invalid_argument("Objective already set.");
  obj = IntConstraint(coefs, vars, negated, -offset);
}

void ILP::setAssumption(const IntVar* iv, const std::vector<bigint>& dom) {
  assert(iv);
  if (dom.empty()) {
    throw std::invalid_argument("No possible values given when setting assumptions for " + iv->getName() + ".");
  }
  for (const bigint& vals_i : dom) {
    if (vals_i < iv->getLowerBound() || vals_i > iv->getUpperBound())
      throw std::invalid_argument("Assumption value " + aux::str(vals_i) + " for " + iv->getName() +
                                  " exceeds variable bounds.");
  }
  for (Var v : iv->getEncodingVars()) {
    assumptions.remove(v);
    assumptions.remove(-v);
  }
  if (dom.size() == 1) {
    bigint val = dom[0] - iv->getLowerBound();
    if (iv->getEncoding() == Encoding::LOG) {
      for (const Var v : iv->getEncodingVars()) {
        assumptions.add(val % 2 == 0 ? -v : v);
        val /= 2;
      }
      assert(val == 0);
    } else if (iv->getEncoding() == Encoding::ORDER) {
      assert(val <= iv->getEncodingVars().size());
      int val_int = static_cast<int>(val);
      if (val_int > 0) {
        assumptions.add(iv->getEncodingVars()[val_int - 1]);
      }
      if (val_int < (int)iv->getEncodingVars().size()) {
        assumptions.add(-iv->getEncodingVars()[val_int]);
      }
    } else {
      assert(iv->getEncoding() == Encoding::ONEHOT);
      assert(val <= iv->getEncodingVars().size());
      int val_int = static_cast<int>(val);
      assumptions.add(iv->getEncodingVars()[val_int]);
    }
    return;
  }
  unordered_set<bigint> toCheck(dom.begin(), dom.end());
  if (toCheck.size() == iv->getUpperBound() - iv->getLowerBound() + 1) return;
  if (iv->getEncoding() != Encoding::ONEHOT) {
    throw std::invalid_argument("Variable " + iv->getName() + " is not one-hot encoded but has " +
                                std::to_string(toCheck.size()) +
                                " (more than one and less than its range) values to assume.");
  }
  bigint val = iv->getLowerBound();
  for (Var v : iv->getEncodingVars()) {
    if (!toCheck.count(val)) {
      assumptions.add(-v);
    }
    ++val;
  }
}

bool ILP::hasAssumption(const IntVar* iv) const {
  return std::any_of(iv->getEncodingVars().begin(), iv->getEncodingVars().end(),
                     [&](Var v) { return assumptions.has(v) || assumptions.has(-v); });
}
std::vector<bigint> ILP::getAssumption(const IntVar* iv) const {
  if (!hasAssumption(iv)) {
    std::vector<bigint> res;
    res.reserve(size_t(iv->getUpperBound() - iv->getLowerBound() + 1));
    for (bigint i = iv->getLowerBound(); i <= iv->getUpperBound(); ++i) {
      res.push_back(i);
    }
    return res;
  }
  assert(hasAssumption(iv));
  if (iv->getEncoding() == Encoding::LOG) {
    bigint val = iv->getLowerBound();
    bigint base = 1;
    for (const Var& v : iv->getEncodingVars()) {
      if (assumptions.has(v)) val += base;
      base *= 2;
    }
    return {val};
  } else if (iv->getEncoding() == Encoding::ORDER) {
    int i = 0;
    for (const Var& v : iv->getEncodingVars()) {
      if (assumptions.has(-v)) break;
      ++i;
    }
    return {iv->getLowerBound() + i};
  }
  assert(iv->getEncoding() == Encoding::ONEHOT);
  std::vector<bigint> res;
  int i = 0;
  for (const Var& v : iv->getEncodingVars()) {
    if (assumptions.has(v)) {
      return {iv->getLowerBound() + i};
    }
    if (!assumptions.has(-v)) {
      res.emplace_back(iv->getLowerBound() + i);
    }
    ++i;
  }
  return res;
}

void ILP::clearAssumptions() { assumptions.clear(); }
void ILP::clearAssumption(const IntVar* iv) {
  for (Var v : iv->getEncodingVars()) {
    assumptions.remove(v);
    assumptions.remove(-v);
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
  Var h = head->getEncodingVars()[0];

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

  Var h = head->getEncodingVars()[0];
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

  Var h = head->getEncodingVars()[0];
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
    aux::appendTo(vars, tup.second->getEncodingVars());
  }
  solver.invalidateLastSol(vars);
}

void ILP::invalidateLastSol(const std::vector<IntVar*>& ivs) {
  if (!hasSolution()) throw std::invalid_argument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(ivs.size());
  for (IntVar* iv : ivs) {
    aux::appendTo(vars, iv->getEncodingVars());
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
  return optim->optimize(assumptions.getKeys());
}

SolveState ILP::runFull(bool stopAtSat, double timeout) {
  if (!initialized()) throw std::invalid_argument("Solver not yet initialized.");
  global.stats.runStartTime = std::chrono::steady_clock::now();
  SolveState result = SolveState::INPROCESSED;
  while ((timeout == 0 || global.stats.getSolveTime() < timeout) &&
         (result == SolveState::INPROCESSED || (result == SolveState::SAT && !stopAtSat))) {
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

std::ostream& ILP::printInput(std::ostream& out) const {
  out << "OBJ ";
  lhs2str(out, obj);
  out << std::endl;
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
    constrs.push_back(aux::str(ic));
  }
  std::sort(constrs.begin(), constrs.end());
  for (const std::string& s : constrs) out << s << std::endl;
  return out;
}

std::ostream& ILP::printVars(std::ostream& out) const {
  for (const auto& v : vars) {
    out << *v << std::endl;
  }
  return out;
}

long long ILP::getNbVars() const { return vars.size(); }

long long ILP::getNbConstraints() const { return reifications.size() + constraints.size(); }

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

unordered_set<IntVar*> ILP::getLastCore() {
  if (!hasCore()) throw std::invalid_argument("No unsat core to return.");

  unordered_set<IntVar*> core;
  if (solver.assumptionsClashWithUnits()) {
    for (Lit l : assumptions.getKeys()) {
      if (isUnit(solver.getLevel(), -l)) core.insert(var2var.at(toVar(l)));
    }
  } else {
    CeSuper clone = solver.lastCore->clone(global.cePools);
    clone->weaken([&](Lit l) { return !assumptions.has(-l); });
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

Ce32 ILP::getSolIntersection(const std::vector<IntVar*>& ivs) {
  global.options.boundUpper.set(false);
  global.options.pureLits.set(false);
  global.options.domBreakLim.set(0);
  SolveState result = SolveState::INPROCESSED;
  while (result == SolveState::INPROCESSED) {
    result = runOnce();
  }
  if (result == SolveState::INCONSISTENT) {
    return nullptr;
  }
  assert(result == SolveState::SAT);

  Ce32 invalidator = global.cePools.take32();
  invalidator->addRhs(1);
  for (IntVar* iv : ivs) {
    for (Var v : iv->getEncodingVars()) {
      invalidator->addLhs(1, -solver.getLastSolution()[v]);
    }
  }
  // NOTE: assumptions and input can overlap, and that is ok
  Var marker = solver.getNbVars() + 1;
  solver.setNbVars(marker, true);
  assumptions.add(-marker);
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
  assumptions.remove(-marker);
  solver.addUnitConstraint(marker, Origin::INVALIDATOR);
  assert(invalidator->isClause());
  invalidator->weaken(marker);
  invalidator->removeZeroes();
  assert(invalidator->getDegree() == 0);
  return invalidator;
}

// NOTE: also throws AsynchronousInterrupt
const std::vector<std::pair<bigint, bigint>> ILP::propagate(const std::vector<IntVar*>& ivs) {
  std::vector<std::pair<bigint, bigint>> consequences;
  Ce32 invalidator = getSolIntersection(ivs);
  if (!invalidator) {  // inconsistent assumptions
    return consequences;
  }

  consequences.reserve(ivs.size());
  for (IntVar* iv : ivs) {
    bigint lb = iv->getLowerBound();
    bigint ub = iv->getUpperBound();
    if (iv->getEncoding() == Encoding::LOG) {
      bigint ub2 =
          lb;  // NOTE: upper bound is not a nice power of two difference with lower bound, so we cannot easily use it
      bigint coef = 1;
      for (Var v : iv->getEncodingVars()) {
        if (invalidator->hasLit(-v)) {
          lb += coef;
        }
        if (!invalidator->hasLit(v)) {
          ub2 += coef;
        }
        coef *= 2;
      }
      ub = aux::min(ub, ub2);
    } else if (iv->getEncoding() == Encoding::ORDER) {
      int lbi = 0;
      int ubi = 0;
      for (Var v : iv->getEncodingVars()) {
        lbi += invalidator->hasLit(-v);
        ubi -= invalidator->hasLit(v);
      }
      lb += lbi;
      ub += ubi;
    } else {
      assert(iv->getEncoding() == Encoding::ONEHOT);
      int ith = 0;
      for (Var v : iv->getEncodingVars()) {
        if (invalidator->hasLit(-v)) {
          lb = iv->getLowerBound() + ith;
          ub = lb;
          break;
        }
        ++ith;
      }
      if (ub != lb) {
        for (Var v : iv->getEncodingVars()) {
          if (invalidator->hasLit(v)) {
            ++lb;
          } else {
            break;
          }
        }
        for (int j = iv->getEncodingVars().size() - 1; j >= 0; --j) {
          if (invalidator->hasLit(iv->getEncodingVars()[j])) {
            --ub;
          } else {
            break;
          }
        }
      }
    }
    assert(lb <= ub);
    consequences.push_back({lb, ub});
  }
  return consequences;
}

// NOTE: also throws AsynchronousInterrupt
const std::vector<std::vector<bigint>> ILP::pruneDomains(const std::vector<IntVar*>& ivs) {
  std::vector<std::vector<bigint>> doms(ivs.size());
  Ce32 invalidator = getSolIntersection(ivs);
  if (!invalidator) {  // inconsistent assumptions
    return doms;
  }

  for (int i = 0; i < (int)ivs.size(); ++i) {
    IntVar* iv = ivs[i];
    if (iv->getEncodingVars().empty()) {
      assert(iv->getLowerBound() == iv->getUpperBound());
      doms[i].push_back(iv->getLowerBound());
      continue;
    }
    if (iv->getEncodingVars().size() == 1) {
      assert(iv->getEncoding() == Encoding::ORDER);
      Var v = iv->getEncodingVars()[0];
      if (!invalidator->hasLit(-v)) {
        doms[i].push_back(iv->getLowerBound());
      }
      if (!invalidator->hasLit(v)) {
        doms[i].push_back(iv->getUpperBound());
      }
      continue;
    }
    assert(iv->getEncoding() == Encoding::ONEHOT);
    bigint val = iv->getLowerBound();
    for (Var v : iv->getEncodingVars()) {
      if (!invalidator->hasLit(v)) {
        doms[i].push_back(val);
      }
      ++val;
    }
  }
  return doms;
}

void ILP::runOnce(int argc, char** argv) {
  global.stats.startTime = std::chrono::steady_clock::now();
  global.options.parseCommandLine(argc, argv);
  global.logger.activate(global.options.proofLog.get());

  if (global.options.verbosity.get() > 0) {
    std::cout << "c Exact - branch " EXPANDED(GIT_BRANCH) " commit " EXPANDED(GIT_COMMIT_HASH) << std::endl;
  }

  aux::timeCallVoid([&] { parsing::file_read(*this); }, global.stats.PARSETIME);

  if (global.options.noSolve) throw AsynchronousInterrupt();
  if (global.options.printCsvData) global.stats.printCsvHeader();
  if (global.options.verbosity.get() > 0) {
    std::cout << "c " << getSolver().getNbVars() << " vars " << getSolver().getNbConstraints() << " constrs"
              << std::endl;
  }

  global.stats.runStartTime = std::chrono::steady_clock::now();

  init();
  SolveState res = SolveState::INPROCESSED;

  while (res == SolveState::INPROCESSED || res == SolveState::SAT) {
    res = runOnce();
  }
}

}  // namespace xct
