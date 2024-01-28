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

#include "ILP.hpp"
#include <stdexcept>
#include "Optimization.hpp"

namespace xct {

Encoding opt2enc(const std::string& opt) {
  assert(opt == "order" || opt == "log" || opt == "onehot");
  return opt == "order" ? Encoding::ORDER : opt == ("log") ? Encoding::LOG : Encoding::ONEHOT;
}

std::ostream& operator<<(std::ostream& o, const IntVar& x) {
  return o << x.getName() << "[" << x.getLowerBound() << "," << x.getUpperBound() << "]";
}
std::ostream& operator<<(std::ostream& o, const IntTerm& x) {
  return o << (x.c < 0 ? "" : "+") << (x.c == 1 ? "" : aux::str(x.c) + "*") << (x.negated ? "~" : "") << *x.v;
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

std::vector<Lit> val2lits(const IntVar* iv, const bigint& val) {
  const std::vector<Var>& encoding = iv->getEncodingVars();
  std::vector<Lit> res;
  res.reserve(encoding.size());
  if (iv->getEncoding() == Encoding::LOG) {
    bigint value = val - iv->getLowerBound();
    assert(value >= 0);
    for (Var v : encoding) {
      res.push_back(value % 2 == 0 ? -v : v);
      value /= 2;
    }
    assert(value == 0);
    return res;
  }
  assert(val - iv->getLowerBound() <= iv->getEncodingVars().size());
  int val_int = static_cast<int>(val - iv->getLowerBound());
  if (iv->getEncoding() == Encoding::ONEHOT) {
    for (int i = 0; i < (int)encoding.size(); ++i) {
      res.push_back(i == val_int ? encoding[i] : -encoding[i]);
    }
    return res;
  }
  assert(iv->getEncoding() == Encoding::ORDER);
  for (int i = 0; i < (int)encoding.size(); ++i) {
    res.push_back(i < val_int ? encoding[i] : -encoding[i]);
  }
  return res;
}

void log2assumptions(const std::vector<Var>& encoding, const bigint& value, const bigint& lowerbound,
                     xct::IntSet& assumptions) {
  bigint val = value - lowerbound;
  assert(val >= 0);
  for (Var v : encoding) {
    assumptions.add(val % 2 == 0 ? -v : v);
    val /= 2;
  }
  assert(val == 0);
}

IntVar::IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub, Encoding e)
    : name(n), lowerBound(lb), upperBound(ub), encoding(getRange() <= 1 ? Encoding::ORDER : e), propVars(), propVar(0) {
  assert(lb <= ub);

  if (nameAsId) {
    assert(isBoolean());
    Var next = std::stoi(getName());
    solver.setNbVars(next, true);
    encodingVars.emplace_back(next);
  } else {
    const bigint range = getRange();
    assert(range > 1 || encoding == Encoding::ORDER);
    int oldvars = solver.getNbVars();
    int newvars = oldvars + (encoding == Encoding::LOG
                                 ? aux::msb(range) + 1  // TODO: correct?
                                 : static_cast<int>(range) + static_cast<int>(encoding == Encoding::ONEHOT));

    solver.setNbVars(newvars, true);
    for (Var var = oldvars + 1; var <= newvars; ++var) {
      encodingVars.emplace_back(var);
    }
    if (encoding == Encoding::LOG) {  // upper bound constraint
      assert(!encodingVars.empty());
      ConstrSimpleArb csa({}, -range);
      csa.terms.reserve(encodingVars.size());
      bigint base = -1;
      for (const Var v : encodingVars) {
        csa.terms.emplace_back(base, v);
        base *= 2;
      }
      // NOTE: last variable could have a smaller coefficient if the range is not a nice power of two - 1
      // This would actually increase the number of solutions to the constraint. It would also not guarantee that each
      // value for an integer variable had a unique Boolean representation. Bad idea probably.
      solver.addConstraint(csa, Origin::FORMULA);
    } else if (encoding == Encoding::ORDER) {
      assert(!encodingVars.empty() || range == 0);
      for (Var var = oldvars + 1; var < solver.getNbVars(); ++var) {
        solver.addBinaryConstraint(var, -(var + 1), Origin::FORMULA);
      }
    } else {
      assert(!encodingVars.empty());
      assert(encoding == Encoding::ONEHOT);
      ConstrSimple32 cs1({}, 1);
      cs1.terms.reserve(encodingVars.size());
      ConstrSimple32 cs2({}, -1);
      cs2.terms.reserve(encodingVars.size());
      for (int var = oldvars + 1; var <= solver.getNbVars(); ++var) {
        cs1.terms.emplace_back(1, var);
        cs2.terms.emplace_back(-1, var);
      }
      solver.addConstraint(cs1, Origin::FORMULA);
      solver.addConstraint(cs2, Origin::FORMULA);
    }
  }
}

bigint IntVar::getValue(const std::vector<Lit>& sol) const {
  bigint val = getLowerBound();
  if (encoding == Encoding::LOG) {
    bigint base = 1;
    for (Var v : getEncodingVars()) {
      assert(v != 0);
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

Var IntVar::getPropVar() const {
  assert(propVar != 0);  // call getPropVars(solver) first!
  return propVar;
}

const std::vector<Var>& IntVar::getPropVars(Solver& solver) {
  assert(encoding == Encoding::LOG);
  if (propVar == 0) {
    int oldvars = solver.getNbVars();
    int newvars = oldvars + encodingVars.size() + 1;
    solver.setNbVars(newvars, true);
    propVar = oldvars + 1;
    propVars.reserve(encodingVars.size());
    for (Var v = propVar + 1; v <= newvars; ++v) {
      propVars.push_back(v);
    }
    ConstrSimpleArb upperBound;  // M + propVars >= encodingVars + M*propVar
    ConstrSimpleArb lowerBound;  // M*propVar + encodingVars >= propVars
    bigint coef = 1;
    for (int i = 0; i < (int)encodingVars.size(); ++i) {
      upperBound.terms.push_back({coef, propVars[i]});
      upperBound.terms.push_back({-coef, encodingVars[i]});
      lowerBound.terms.push_back({-coef, propVars[i]});
      lowerBound.terms.push_back({coef, encodingVars[i]});
      coef *= 2;
    }
    coef -= 1;
    upperBound.terms.push_back({-coef, propVar});
    upperBound.rhs = -coef;
    solver.addConstraint(upperBound, Origin::FORMULA);
    lowerBound.terms.push_back({coef, propVar});
    lowerBound.rhs = 0;
    solver.addConstraint(lowerBound, Origin::FORMULA);
  }
  return propVars;
}

IntConstraint::IntConstraint() : lowerBound(0) {}

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

const std::vector<IntTerm>& IntConstraint::getLhs() const { return lhs; }
const std::optional<bigint>& IntConstraint::getLB() const { return lowerBound; }
const std::optional<bigint>& IntConstraint::getUB() const { return upperBound; }

const bigint IntConstraint::getRange() const {
  bigint res = 0;
  for (const IntTerm& t : lhs) {
    assert(t.v->getRange() >= 0);
    res += aux::abs(t.c) * t.v->getRange();
  }
  return res;
}

int64_t IntConstraint::size() const { return lhs.size(); }

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
    if (t.v->getEncoding() == Encoding::LOG) {
      assert(!t.v->getEncodingVars().empty());
      bigint base = 1;
      for (const Var v : t.v->getEncodingVars()) {
        input->addLhs(base * t.c, v);
        base *= 2;
      }
    } else if (t.v->getEncoding() == Encoding::ORDER) {
      assert(t.v->getRange() == 0 || !t.v->getEncodingVars().empty());
      for (const Var v : t.v->getEncodingVars()) {
        input->addLhs(t.c, v);
      }
    } else {
      assert(t.v->getEncoding() == Encoding::ONEHOT);
      assert(!t.v->getEncodingVars().empty());
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

ILP::ILP(const Options& opts, bool keepIn) : global(opts), solver(global), obj({}, {}, {}, 0), keepInput(keepIn) {
  global.stats.startTime = std::chrono::steady_clock::now();
  aux::rng::seed = global.options.randomSeed.get();
  global.logger.activate(global.options.proofLog.get(), (bool)global.options.proofZip);
  setObjective({}, {}, {});
}

Solver& ILP::getSolver() { return solver; }
void ILP::setMaxSatVars() { maxSatVars = solver.getNbVars(); }
int ILP::getMaxSatVars() const { return maxSatVars; }

IntVar* ILP::addVar(const std::string& name, const bigint& lowerbound, const bigint& upperbound, Encoding encoding,
                    bool nameAsId) {
  assert(!getVarFor(name));
  if (upperbound < lowerbound) {
    throw InvalidArgument((std::stringstream() << "Upper bound " << upperbound << " of " << name
                                               << " is smaller than lower bound " << lowerbound)
                              .str());
  }
  vars.push_back(std::make_unique<IntVar>(name, solver, nameAsId, lowerbound, upperbound, encoding));
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
  if (coefs.size() != vars.size() || (!negated.empty() && negated.size() != vars.size())) {
    throw InvalidArgument("Coefficient, variable, or negated lists differ in size.");
  }

  obj = IntConstraint(coefs, vars, negated, -offset);
  optim = OptimizationSuper::make(obj, solver, assumptions);
}

void ILP::setAssumption(const IntVar* iv, const std::vector<bigint>& dom) {
  assert(iv);
  if (dom.empty()) {
    throw InvalidArgument("No possible values given when setting assumptions for " + iv->getName() + ".");
  }
  for (const bigint& vals_i : dom) {
    if (vals_i < iv->getLowerBound() || vals_i > iv->getUpperBound())
      throw InvalidArgument("Assumption value " + aux::str(vals_i) + " for " + iv->getName() +
                            " exceeds variable bounds.");
  }
  for (Var v : iv->getEncodingVars()) {
    assumptions.remove(v);
    assumptions.remove(-v);
  }
  if (dom.size() == 1) {
    if (iv->getEncoding() == Encoding::LOG) {
      log2assumptions(iv->getEncodingVars(), dom[0], iv->getLowerBound(), assumptions);
    } else {
      assert(dom[0] - iv->getLowerBound() <= iv->getEncodingVars().size());
      int val_int = static_cast<int>(dom[0] - iv->getLowerBound());
      if (iv->getEncoding() == Encoding::ORDER) {
        if (val_int > 0) {
          assumptions.add(iv->getEncodingVars()[val_int - 1]);
        }
        if (val_int < (int)iv->getEncodingVars().size()) {
          assumptions.add(-iv->getEncodingVars()[val_int]);
        }
      } else {
        assert(iv->getEncoding() == Encoding::ONEHOT);
        assumptions.add(iv->getEncodingVars()[val_int]);
      }
    }
  } else {
    unordered_set<bigint> toCheck(dom.begin(), dom.end());
    if (toCheck.size() == iv->getUpperBound() - iv->getLowerBound() + 1) return;
    if (iv->getEncoding() != Encoding::ONEHOT) {
      throw InvalidArgument("Variable " + iv->getName() + " is not one-hot encoded but has " +
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
  optim = OptimizationSuper::make(obj, solver, assumptions);
}

void ILP::setAssumption(const IntVar* iv, bool val) {
  assert(iv);
  assert(iv->isBoolean());
  for (Var v : iv->getEncodingVars()) {
    assumptions.remove(v);
    assumptions.remove(-v);
  }
  Var v = iv->getEncodingVars()[0];
  if (val) {
    assumptions.remove(-v);
    assumptions.add(v);
  } else {
    assumptions.remove(v);
    assumptions.add(-v);
  }
  optim = OptimizationSuper::make(obj, solver, assumptions);
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

void ILP::clearAssumptions() {
  assumptions.clear();
  optim = OptimizationSuper::make(obj, solver, assumptions);
}
void ILP::clearAssumption(const IntVar* iv) {
  for (Var v : iv->getEncodingVars()) {
    assumptions.remove(v);
    assumptions.remove(-v);
  }
  optim = OptimizationSuper::make(obj, solver, assumptions);
}

void ILP::setSolutionHints(const std::vector<IntVar*>& ivs, const std::vector<bigint>& vals) {
  assert(ivs.size() == vals.size());
  std::vector<std::pair<Var, Lit>> hints;
  for (int i = 0; i < (int)ivs.size(); ++i) {
    IntVar* iv = ivs[i];
    assert(iv);
    const bigint& vals_i = vals[i];
    assert(vals_i >= iv->getLowerBound());
    assert(vals_i <= iv->getUpperBound());
    for (Lit l : val2lits(iv, vals_i)) {
      assert(l != 0);
      hints.emplace_back(toVar(l), l);
    }
  }
  solver.fixPhase(hints, true);
}
void ILP::clearSolutionHints(const std::vector<IntVar*>& ivs) {
  std::vector<std::pair<Var, Lit>> hints;
  for (const IntVar* iv : ivs) {
    for (const Var& v : iv->getEncodingVars()) {
      hints.emplace_back(v, 0);
    }
  }
  solver.fixPhase(hints);
}

void ILP::addConstraint(const IntConstraint& ic) {
  if (ic.size() > 1e9) throw InvalidArgument("Constraint has more than 1e9 terms.");
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
void ILP::addReification(IntVar* head, const IntConstraint& ic) {
  addLeftReification(head, ic);
  addRightReification(head, ic);
}

// head => rhs -- head implies rhs
void ILP::addRightReification(IntVar* head, const IntConstraint& ic) {
  if (ic.size() >= 1e9) throw InvalidArgument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw InvalidArgument("Head of reification is not Boolean.");

  if (keepInput) reifications.push_back({head, ic});

  bool run[2] = {ic.getUB().has_value(), ic.getLB().has_value()};
  for (int i = 0; i < 2; ++i) {
    if (!run[i]) continue;
    CeArb leq = global.cePools.takeArb();
    ic.toConstrExp(leq, i);
    leq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, global.stats);

    Var h = head->getEncodingVars()[0];
    leq->addLhs(leq->degree, -h);
    solver.addConstraint(leq, Origin::FORMULA);
  }
}

// head <= rhs -- rhs implies head
void ILP::addLeftReification(IntVar* head, const IntConstraint& ic) {
  if (ic.size() >= 1e9) throw InvalidArgument("Reification has more than 1e9 terms.");
  if (!head->isBoolean()) throw InvalidArgument("Head of reification is not Boolean.");

  if (keepInput) reifications.push_back({head, ic});

  bool run[2] = {ic.getUB().has_value(), ic.getLB().has_value()};
  for (int i = 0; i < 2; ++i) {
    if (!run[i]) continue;
    CeArb geq = global.cePools.takeArb();
    ic.toConstrExp(geq, i);
    geq->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, global.stats);

    Var h = head->getEncodingVars()[0];
    geq->addRhs(-1);
    geq->invert();
    geq->addLhs(geq->degree, h);
    solver.addConstraint(geq, Origin::FORMULA);
  }
}

void ILP::fix(IntVar* iv, const bigint& val) { addConstraint(IntConstraint{{1}, {iv}, {false}, val, val}); }

void ILP::boundObjByLastSol() {
  if (!hasSolution()) throw InvalidArgument("No solution to add objective bound.");
  optim->boundObjectiveBySolution(solver.getLastSolution());
}

void ILP::invalidateLastSol() {
  if (!hasSolution()) throw InvalidArgument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(name2var.size());
  for (const auto& tup : name2var) {
    aux::appendTo(vars, tup.second->getEncodingVars());
  }
  solver.invalidateLastSol(vars);
}

void ILP::invalidateLastSol(const std::vector<IntVar*>& ivs, Var flag) {
  if (!hasSolution()) throw InvalidArgument("No solution to add objective bound.");

  std::vector<Var> vars;
  vars.reserve(ivs.size() + (flag != 0));
  for (IntVar* iv : ivs) {
    aux::appendTo(vars, iv->getEncodingVars());
  }
  if (flag != 0) {
    vars.push_back(flag);
  }
  solver.invalidateLastSol(vars);
}

bool ILP::reachedTimeout(double timeout) const { return timeout != 0 && global.stats.getRunTime() > timeout; }

SolveState ILP::runOnce(bool optimize) {  // NOTE: also throws AsynchronousInterrupt and UnsatEncounter
  return optim->run(optimize);
}

SolveState ILP::runFull(bool optimize, double timeout) {
  global.stats.runStartTime = std::chrono::steady_clock::now();
  SolveState result = SolveState::INPROCESSED;
  if (global.options.verbosity.get() > 0) {
    std::cout << "c #vars " << solver.getNbVars() << " #constraints " << solver.getNbConstraints() << std::endl;
  }
  while (!reachedTimeout(timeout) && (result == SolveState::INPROCESSED || (result == SolveState::SAT && optimize))) {
    result = runOnce(optimize);
  }
  return reachedTimeout(timeout) ? SolveState::TIMEOUT : result;
}

void ILP::printFormula() { printFormula(std::cout); }

std::ostream& ILP::printFormula(std::ostream& out) {
  int nbConstraints = 0;
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    nbConstraints += isNonImplied(c.getOrigin());
  }
  out << "* #variable= " << solver.getNbVars() << " #constraint= " << nbConstraints << "\n";
  if (optim->getOrigObj()->nVars() > 0) {
    out << "min: ";
    optim->getOrigObj()->toStreamAsOPBlhs(out, true);
    out << ";\n";
  }
  for (Lit l : solver.getUnits()) {
    out << std::pair<int, Lit>{1, l} << " >= 1 ;\n";
  }
  for (Var v = 1; v <= solver.getNbVars(); ++v) {
    if (solver.getEqualities().isCanonical(v)) continue;
    out << std::pair<int, Lit>{1, v} << " " << std::pair<int, Lit>{-1, solver.getEqualities().getRepr(v).l}
        << " = 0 ;\n";
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

bigint ILP::getSolSpaceSize() const {
  bigint total = 0;
  for (const std::unique_ptr<IntVar>& v : vars) {
    total += aux::msb(1 + v->getRange());
  }
  return total;
};

ratio ILP::getLowerBound() const { return static_cast<ratio>(optim->getLowerBound()); }
ratio ILP::getUpperBound() const { return static_cast<ratio>(optim->getUpperBound()); }

bool ILP::hasSolution() const {
  assert(optim->solutionsFound == 0 || solver.foundSolution());
  return optim->solutionsFound > 0;
}

void ILP::clearSolution() { optim->solutionsFound = 0; }

bigint ILP::getLastSolutionFor(IntVar* iv) const {
  if (!hasSolution()) throw InvalidArgument("No solution to return.");
  return iv->getValue(solver.getLastSolution());
}

std::vector<bigint> ILP::getLastSolutionFor(const std::vector<IntVar*>& vars) const {
  if (!hasSolution()) throw InvalidArgument("No solution to return.");
  return aux::comprehension(vars, [&](IntVar* iv) { return getLastSolutionFor(iv); });
}

bool ILP::hasCore() const { return solver.lastCore || solver.assumptionsClashWithUnits(); }

unordered_set<IntVar*> ILP::getLastCore() {
  if (!hasCore()) throw InvalidArgument("No unsat core to return.");

  unordered_set<IntVar*> core;
  if (solver.assumptionsClashWithUnits()) {
    for (Lit l : assumptions.getKeys()) {
      if (isUnit(solver.getLevel(), -l)) core.insert(var2var.at(toVar(l)));
    }
    assert(!core.empty());
  } else {
    CeSuper clone = solver.lastCore->clone(global.cePools);
    clone->weaken([&](Lit l) { return !assumptions.has(-l); });
    clone->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    clone->simplifyToClause();
    for (Var v : clone->vars) {
      core.insert(var2var.at(v));
    }
  }
  return core;
}

void ILP::clearCore() { solver.lastCore.reset(); }

void ILP::printOrigSol() const {
  if (!hasSolution()) throw InvalidArgument("No solution to return.");
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->getValue(solver.getLastSolution());
    if (val != 0) {
      std::cout << iv->getName() << " " << val << "\n";
    }
  }
}

std::pair<SolveState, Ce32> ILP::getSolIntersection(const std::vector<IntVar*>& ivs, bool keepstate, double timeout) {
  SolveState result = runFull(false, timeout);
  if (result == SolveState::INCONSISTENT || result == SolveState::UNSAT || result == SolveState::TIMEOUT) {
    return {result, CeNull()};
  }
  assert(result == SolveState::SAT);
  auto [result2, opt] = toOptimum(keepstate, timeout);
  if (result2 == SolveState::TIMEOUT) {
    return {SolveState::TIMEOUT, CeNull()};
  }

  Ce32 invalidator = global.cePools.take32();
  invalidator->addRhs(1);
  for (IntVar* iv : ivs) {
    for (Var v : iv->getEncodingVars()) {
      invalidator->addLhs(1, -solver.getLastSolution()[v]);
    }
  }
  // NOTE: assumptions and input can overlap, and that is ok

  Var marker = 0;
  Optim old;
  if (keepstate) {
    IntVar* flag = fixObjective(obj, opt);
    marker = flag->getEncodingVars()[0];
    invalidator->addLhs(1, -marker);
    assert(invalidator->isClause());
    old = std::move(optim);
    optim = OptimizationSuper::make(IntConstraint(), solver, assumptions);
  }

  result = runFull(false, timeout);
  assert(result == SolveState::SAT || result == SolveState::TIMEOUT);
  if (result == SolveState::SAT) {
    while (true) {
      solver.addConstraint(invalidator, Origin::INVALIDATOR);
      result = runFull(false, timeout);
      if (result != SolveState::SAT) break;
      for (Var v : invalidator->getVars()) {
        Lit invallit = invalidator->getLit(v);
        if (solver.getLastSolution()[v] == invallit) {  // solution matches invalidator
          invalidator->addLhs(-1, invallit);
        }
      }
      invalidator->removeZeroes();
    }
  }

  if (keepstate) {
    assert(marker != 0);
    invalidator->addLhs(-1, -marker);
    invalidator->removeZeroes();
    assumptions.remove(marker);
    solver.addUnitConstraint(-marker, Origin::INVALIDATOR);
    optim = std::move(old);
  }
  assert(invalidator->isClause());

  assert(result != SolveState::INPROCESSED);
  assert(result != SolveState::SAT);
  if (result == SolveState::TIMEOUT) return {SolveState::TIMEOUT, CeNull()};
  assert(result == SolveState::INCONSISTENT || result == SolveState::UNSAT);
  return {result, invalidator};
}

IntVar* ILP::addFlag() {
  // TODO: ensure unique variable names
  return addVar("__flag" + std::to_string(solver.getNbVars() + 1), 0, 1, Encoding::ORDER);
}

std::pair<SolveState, bigint> ILP::toOptimum(bool keepstate, double timeout) {
  Optim old = std::move(optim);
  IntVar* flag = addFlag();
  assert(flag->getEncodingVars().size() == 1);
  Var flag_v = flag->getEncodingVars()[0];
  assumptions.add(flag_v);
  bigint cf = keepstate ? obj.getRange() : 1;
  obj.lhs.emplace_back(cf, flag, false);
  optim = OptimizationSuper::make(obj, solver, assumptions);
  SolveState res = runFull(true, timeout);
  bigint bound = optim->getUpperBound() - cf;
  assert(obj.lhs.back().v == flag);
  obj.lhs.pop_back();
  assumptions.remove(flag_v);
  optim = std::move(old);
  solver.addUnitConstraint(-flag_v, Origin::FORMULA);
  return {res, bound};
}

// TODO: fix optimization with assumption variable
// TODO: refactor this when optimization works well with user-given assumptions
std::pair<SolveState, bigint> ILP::optimizeVar(IntVar* iv, const bigint& startbound, bool minimize, double timeout) {
  bigint currentbound = startbound;
  int offset = minimize ? -1 : 1;
  while (true) {
    currentbound += offset;
    log2assumptions(iv->getPropVars(solver), currentbound, iv->getLowerBound(), assumptions);
    assumptions.add(minimize ? iv->getPropVar() : -iv->getPropVar());
    SolveState state = SolveState::INPROCESSED;
    while (state == SolveState::INPROCESSED) {
      if (reachedTimeout(timeout)) return {SolveState::TIMEOUT, currentbound - offset};
      state = runOnce(false);
    }
    assert(state != SolveState::INPROCESSED);
    assert(state != SolveState::UNSAT);  // should have been caught previously
    for (Var v : iv->getPropVars(solver)) {
      assumptions.remove(v);
      assumptions.remove(-v);
      assumptions.remove(iv->getPropVar());
      assumptions.remove(-iv->getPropVar());
    }
    if (state == SolveState::TIMEOUT) {
      return {SolveState::TIMEOUT, currentbound - offset};
    }
    if (state == SolveState::INCONSISTENT) {
      return {SolveState::SAT, currentbound - offset};
    }
    assert(state == SolveState::SAT);
    bigint newVal = iv->getValue(solver.getLastSolution());
    assert(!minimize || newVal <= currentbound);
    assert(minimize || newVal >= currentbound);
    currentbound = newVal;
    if (minimize && currentbound == iv->getLowerBound()) return {SolveState::SAT, currentbound};
    if (!minimize && currentbound == iv->getUpperBound()) return {SolveState::SAT, currentbound};
  }
}

// NOTE: also throws AsynchronousInterrupt
const std::vector<std::pair<bigint, bigint>> ILP::propagate(const std::vector<IntVar*>& ivs, bool keepstate,
                                                            double timeout) {
  auto [state, invalidator] = getSolIntersection(ivs, keepstate, timeout);
  if (state == SolveState::TIMEOUT || state == SolveState::UNSAT || state == SolveState::INCONSISTENT) {
    assert(!invalidator);
    return {};
  }
  std::vector<std::pair<bigint, bigint>> consequences;
  consequences.reserve(ivs.size());
  for (IntVar* iv : ivs) {
    bigint lb = iv->getLowerBound();
    bigint ub = iv->getUpperBound();
    if (iv->getEncoding() == Encoding::LOG) {
      bigint ub2 = lb;
      // NOTE: upper bound is not a nice power of two difference with lower bound, so we cannot easily use it
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
      if (ub != lb) {
        // we probably only have an approximate propagation, let's get the real one
        auto [state, newlb] = optimizeVar(iv, ub, true, timeout);
        if (state == SolveState::TIMEOUT) {
          return {};
        } else {
          lb = newlb;
        }
        auto [state2, newub] = optimizeVar(iv, lb, false, timeout);
        if (state2 == SolveState::TIMEOUT) {
          return {};
        } else {
          ub = newub;
        }
      }
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
const std::vector<std::vector<bigint>> ILP::pruneDomains(const std::vector<IntVar*>& ivs, bool keepstate,
                                                         double timeout) {
  for (IntVar* iv : ivs) {
    if (iv->getEncodingVars().size() != 1 && iv->getEncoding() != Encoding::ONEHOT) {
      throw InvalidArgument("Non-Boolean variable " + iv->getName() +
                            " is passed to pruneDomains but is not one-hot encoded.");
    }
  }
  auto [state, invalidator] = getSolIntersection(ivs, keepstate, timeout);
  if (state == SolveState::TIMEOUT) {
    return {};
  }
  std::vector<std::vector<bigint>> doms(ivs.size());
  if (state == SolveState::UNSAT || state == SolveState::INCONSISTENT) {
    assert(!invalidator);
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

IntVar* ILP::fixObjective(const IntConstraint& ico, const bigint& optval) {
  IntVar* flag = addFlag();
  IntConstraint ic = ico;
  assert(ico.getLB().has_value());
  ic.upperBound = optval + ico.getLB().value();
  ic.lowerBound.reset();
  addRightReification(flag, ic);
  assumptions.add(flag->getEncodingVars()[0]);
  return flag;
}

std::pair<SolveState, int64_t> ILP::count(const std::vector<IntVar*>& ivs, bool keepstate, double timeout) {
  if (global.options.verbosity.get() > 0) {
    std::cout << "c #vars " << solver.getNbVars() << " #constraints " << solver.getNbConstraints() << std::endl;
  }
  bigint optval = 0;
  if (obj.size() > 0) {
    std::pair<SolveState, bigint> tmp = toOptimum(keepstate, timeout);
    optval = tmp.second;
  }

  Optim old;
  Var flag_v = 0;
  if (keepstate) {
    old = std::move(optim);
    IntVar* flag = fixObjective(obj, optval);
    flag_v = flag->getEncodingVars()[0];
    optim = OptimizationSuper::make(IntConstraint(), solver, assumptions);
  }
  int64_t n = 0;
  SolveState result = SolveState::SAT;
  while (true) {
    result = runFull(false, timeout);
    if (result != SolveState::SAT) break;
    ++n;
    invalidateLastSol(ivs, flag_v);
  }

  if (keepstate) {
    assert(assumptions.has(flag_v));
    assumptions.remove(flag_v);
    solver.addUnitConstraint(-flag_v, Origin::FORMULA);
    optim = std::move(old);
  }

  if (result == SolveState::TIMEOUT) {
    return {SolveState::TIMEOUT, -1 - n};
  } else {
    return {result, n};
  }
}

void ILP::runInternal(int argc, char** argv) {
  global.stats.startTime = std::chrono::steady_clock::now();

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
  SolveState res = SolveState::INPROCESSED;
  while (res == SolveState::INPROCESSED || res == SolveState::SAT) {
    res = optim->run(true);
  }
}

}  // namespace xct
