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
    : name(n), lowerBound(lb), upperBound(ub), logEncoding(false) {
  assert(lb <= ub);
  assert(!nameAsId || isBoolean());

  if (nameAsId) {
    Var next = std::stoi(getName());
    solver.setNbVars(next, true);
    encoding.emplace_back(next);
  } else {
    bigint range = getRange();
    if (range != 0) {
      logEncoding = range > options.intEncoding.get();
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
        solver.addConstraintUnchecked(ConstrSimpleArb({lhs}, -getRange()), Origin::FORMULA);
      } else {  // binary order constraints
        for (Var var = oldvars + 1; var < oldvars + newvars; ++var) {
          solver.addConstraintUnchecked(ConstrSimple32({{1, var}, {1, -var - 1}}, 1), Origin::FORMULA);
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
  return iv;
}

bool ILP::hasVarFor(const std::string& name) const { return name2var.count(name); }

void ILP::setObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const std::vector<bool>& negated, const bigint& mult, const bigint& offset) {
  assert(!optim);
  obj = IntConstraint(coefs, vars, negated, -offset);
  objmult = mult;
}

void ILP::setAssumptions(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                         const std::vector<bool>& negated) {
  // TODO
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

void ILP::init() {
  asynch_interrupt = false;
  aux::rng::seed = options.randomSeed.get();
  CeArb o = cePools.takeArb();
  obj.toConstrExp(o, true);
  solver.init(o);
  optim = OptimizationSuper::make(o, solver);
}

SolveState ILP::run() {
  try {
    return optim->optimize();
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
    std::cout << "min: ";
    for (const IntTerm& it : getObjective().getLhs()) {
      std::cout << (it.c < 0 ? "" : "+") << it.c << " x" << it.v->getName() << " ";
    }
    std::cout << ";\n";
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

void ILP::printOrigSol() const {
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->getValue(solver.getLastSolution());
    if (val != 0) {
      std::cout << iv->getName() << " " << val << "\n";
    }
  }
}

ratio ILP::getLowerBound() const { return static_cast<ratio>(optim->getLowerBound()) / objmult; }
ratio ILP::getUpperBound() const { return static_cast<ratio>(optim->getUpperBound()) / objmult; }
bool ILP::hasSolution() const {
  bool result = optim && optim->solutionsFound > 0;
  assert(result == solver.foundSolution());  // TODO: check behavior on empty formula
  return result;
}

}  // namespace xct
