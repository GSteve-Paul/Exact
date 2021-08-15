/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "ILP.hpp"
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
std::ostream& operator<<(std::ostream& o, const ILP& x) {
  o << "obj: " << x.getObjective();
  for (const IntConstraint& c : x.getConstraints()) o << "\n" << c;
  return o;
}

IntVar::IntVar(const std::string& n, Solver& solver, bool nameAsId, const bigint& lb, const bigint& ub)
    : name(n), lowerBound(lb), upperBound(ub), logEncoding(getRange() > options.intEncoding.get()) {
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
  assert(negated.size() == 0 || negated.size() == coefs.size());
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
  assert(lowerbound <= upperbound);
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

void ILP::setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const std::vector<bool>& negated, const bigint& mult, const bigint& offset) {
  assert(!optim);
  obj = IntConstraint(coefs, vars, negated, -offset);
  objmult = mult;
}

void ILP::setAssumptions(const std::vector<bigint>& vals, const std::vector<IntVar*>& vars) {
  assert(vals.size() == vars.size());
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
  assert(coefs.size() == vars.size());
  constrs.emplace_back(coefs, vars, negated, lb, ub);

  IntConstraint ic = constrs.back();
  if (ic.getLB().has_value()) {
    CeArb input = cePools.takeArb();
    ic.toConstrExp(input, true);
    if (solver.addConstraint(input, Origin::FORMULA).second == ID_Unsat) return State::UNSAT;
  }
  if (ic.getUB().has_value()) {
    CeArb input = cePools.takeArb();
    ic.toConstrExp(input, false);
    if (solver.addConstraint(input, Origin::FORMULA).second == ID_Unsat) return State::UNSAT;
  }
  return State::SUCCESS;
}

State ILP::addLastSolObjectiveBound() {
  if (!hasSolution()) return State::FAIL;
  return optim->handleNewSolution(solver.getLastSolution());
}

State ILP::addLastSolInvalidatingClause() {
  if (!hasSolution()) return State::FAIL;
  std::pair<ID, ID> ids = solver.addLastSolInvalidatingClause();
  return ids.second == ID_Unsat ? State::UNSAT : State::SUCCESS;
}

void ILP::init(bool onlyFormulaDerivations) {
  if (onlyFormulaDerivations) {
    options.pureLits.parse("0");
    options.domBreakLim.parse("0");
    options.boundUpper.parse("0");
  }
  asynch_interrupt = false;
  aux::rng::seed = options.randomSeed.get();
  CeArb o = cePools.takeArb();
  obj.toConstrExp(o, true);
  solver.init(o);
  optim = OptimizationSuper::make(o, solver);
}

SolveState ILP::run() {
  try {
    return optim->optimize(assumptions);
  } catch (const AsynchronousInterrupt& ai) {
    if (options.outputMode.is("default")) std::cout << "c " << ai.what() << std::endl;
    return SolveState::INTERRUPTED;
  }
}

void ILP::printFormula() {
  int nbConstraints = 0;
  for (const CRef& cr : solver.getRawConstraints()) {
    const Constr& c = solver.getCA()[cr];
    nbConstraints += isNonImplied(c.getOrigin());
  }
  std::cout << "* #variable= " << solver.getNbVars() << " #constraint= " << nbConstraints << "\n";
  if (hasObjective()) {
    std::cout << "min: " << optim->getReformObj() << "\n";
  }
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
  return hasObjective() ? static_cast<ratio>(optim->getLowerBound()) / objmult : static_cast<ratio>(0);
}
ratio ILP::getUpperBound() const {
  return hasObjective() ? static_cast<ratio>(optim->getUpperBound()) / objmult : static_cast<ratio>(0);
}

bool ILP::hasSolution() const {
  bool result = optim && optim->solutionsFound > 0;
  assert(result == solver.foundSolution());  // TODO: check behavior on empty formula
  return result;
}

std::vector<long long> ILP::getLastSolutionFor(const std::vector<std::string>& vars) const {
  std::vector<long long> result;
  result.reserve(vars.size());
  for (const std::string& var : vars) {
    bigint val = name2var.at(var)->getValue(solver.getLastSolution());
    assert(val <= std::numeric_limits<long long>::max());
    assert(val >= std::numeric_limits<long long>::lowest());
    result.push_back(static_cast<long long>(val));
  }
  return result;
}

bool ILP::hasCore() const { return solver.assumptionsClashWithUnits() || solver.lastCore; }

std::vector<std::string> ILP::getLastCore() const {
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

}  // namespace xct
