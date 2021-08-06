/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "ILP.hpp"
#include "Optimization.hpp"

namespace rs {

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
  o << "obj: " << x.obj;
  for (const IntConstraint& c : x.constrs) o << "\n" << c;
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

IntVar* ILP::getVarFor(const std::string& name, bool nameAsId, const bigint& lowerbound, const bigint& upperbound) {
  if (auto it = name2var.find(name); it != name2var.end()) return it->second;
  assert(lowerbound <= upperbound);
  vars.push_back(std::make_unique<IntVar>(name, solver, nameAsId, lowerbound, upperbound));
  IntVar* iv = vars.back().get();
  name2var.insert({name, iv});
  return iv;
}

bool ILP::hasVarFor(const std::string& name) const { return name2var.count(name); }

void ILP::addObjective(const std::vector<bigint>& coefs, const std::vector<IntVar*>& vars,
                       const std::vector<bool>& negated, const bigint& mult, const bigint& offset) {
  assert(!hasObjective());
  obj = IntConstraint(coefs, vars, negated, -offset);
  objmult = mult;
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
  CeArb o = cePools.takeArb();
  obj.toConstrExp(o, true);
  solver.init(o);
  optim = OptimizationSuper::make(o);
}

State ILP::run() { return optim->optimize(); }

void ILP::printOrigSol(const std::vector<Lit>& sol) {
  std::unordered_set<Var> trueVars;
  for (Lit l : sol) {
    if (l > 0) {
      trueVars.insert(l);
    }
  }
  for (const std::unique_ptr<IntVar>& iv : vars) {
    bigint val = iv->getLowerBound();
    if (iv->usesLogEncoding()) {
      bigint base = 1;
      for (Var v : iv->encodingVars()) {
        if (trueVars.count(v)) {
          val += base;
        }
        base *= 2;
      }
    } else {
      int sum = 0;
      for (Var v : iv->encodingVars()) {
        sum += trueVars.count(v);
      }
      val += sum;
    }
    if (val != 0) {
      std::cout << iv->getName() << " " << val << "\n";
    }
  }
}

bool ILP::hasUpperBound() const {
  bool result = optim && optim->solutionsFound > 0;
  assert(result == solver.foundSolution());  // TODO: check behavior on empty formula
  return result;
}
ratio ILP::getUpperBound() const {
  return hasUpperBound() ? static_cast<ratio>(optim->bestObjSoFar) / objmult : static_cast<ratio>(0);
}

bool ILP::hasSolution() const { return hasUpperBound(); }

}  // namespace rs
