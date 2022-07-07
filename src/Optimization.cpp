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

/**********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**********************************************************************/

#include "Optimization.hpp"
#include "ILP.hpp"
#include "constraints/ConstrExp.hpp"

namespace xct {

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::LazyVar(Solver& slvr, const Ce32& cardCore, Var startVar, const SMALL& m, const LARGE& esum,
                               const LARGE& normUpBnd)
    : solver(slvr), coveredVars(cardCore->getDegree()), upperBound(cardCore->absCoeffSum()), mult(m), exceedSum(esum) {
  setUpperBound(normUpBnd);
  cardCore->toSimple()->copyTo(atLeast);
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore->getDegree());
  atMost.rhs = -atLeast.rhs;
  atMost.terms.reserve(atLeast.size());
  for (auto& t : atLeast.terms) {
    atMost.terms.emplace_back(-t.c, t.l);
  }
  currentVar = startVar;
  atLeast.terms.emplace_back(-1, startVar);
  atMost.terms.emplace_back(remainingVars(), startVar);
  ++coveredVars;
}

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

template <typename SMALL, typename LARGE>
int LazyVar<SMALL, LARGE>::remainingVars() const {
  return upperBound - coveredVars;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::setUpperBound(const LARGE& normalizedUpperBound) {
  upperBound = static_cast<int>(std::min<LARGE>(upperBound, (normalizedUpperBound + exceedSum) / mult));
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addVar(Var v) {
  currentVar = v;
  atLeast.terms.emplace_back(-1, v);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  atMost.terms.emplace_back(remainingVars(), v);
  ++coveredVars;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addAtLeastConstraint() {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, true, false);  // TODO: should old constraints be force deleted?
  solver.addConstraintUnchecked(atLeast, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addAtMostConstraint() {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, true, false);
  solver.addConstraintUnchecked(atMost, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  solver.addConstraintUnchecked(ConstrSimple32({{1, prevvar}, {1, -currentVar}}, 1), Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addFinalAtMost() {
  solver.dropExternal(atMostID, true, false);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  solver.addConstraintUnchecked(atMost, Origin::COREGUIDED);
}

OptimizationSuper::OptimizationSuper(Solver& s, ILP& i) : solver(s), ilp(i) {}

Optim OptimizationSuper::make(const CeArb& obj, Solver& solver, ILP& ilp) {
  bigint maxVal = obj->getCutoffVal() * INF;  // INF factor allows adding log-encoded core to the objective
  if (maxVal <= static_cast<bigint>(limitAbs<int, long long>())) {  // TODO: try to internalize this check in ConstrExp
    Ce32 o = ilp.cePools.take32();
    obj->copyTo(o);
    return std::make_shared<Optimization<int, long long>>(o, solver, ilp);
  } else if (maxVal <= static_cast<bigint>(limitAbs<long long, int128>())) {
    Ce64 o = ilp.cePools.take64();
    obj->copyTo(o);
    return std::make_shared<Optimization<long long, int128>>(o, solver, ilp);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int128>())) {
    Ce96 o = ilp.cePools.take96();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int128>>(o, solver, ilp);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int256>())) {
    Ce128 o = ilp.cePools.take128();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int256>>(o, solver, ilp);
  } else {
    CeArb o = ilp.cePools.takeArb();
    obj->copyTo(o);
    return std::make_shared<Optimization<bigint, bigint>>(o, solver, ilp);
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(const CePtr<SMALL, LARGE>& obj, Solver& s, ILP& i)
    : OptimizationSuper(s, i), origObj(obj), somethingHappened(false), firstRun(true) {
  // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  lower_bound = -origObj->getDegree();
  upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

  reformObj = ilp.cePools.take<SMALL, LARGE>();
  origObj->copyTo(reformObj);
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  reformObj->removeEqualities(solver.getEqualities(), false);
  if (ilp.stats.DEPLTIME.z == -1 &&
      std::none_of(reformObj->getVars().begin(), reformObj->getVars().end(), [&](Var v) { return solver.isOrig(v); })) {
    ilp.stats.DEPLTIME.z = ilp.stats.getTime();
  }

  reply = SolveState::INPROCESSED;
  stratDiv = ilp.options.cgStrat.get();
  stratLim = stratDiv == 1 ? 1 : aux::toDouble(reformObj->getLargestCoef());
  coreguided = ilp.options.cgHybrid.get() >= 1;
};

template <typename SMALL, typename LARGE>
CeSuper Optimization<SMALL, LARGE>::getReformObj() const {
  return reformObj;
};

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::printObjBounds() {
  if (ilp.options.verbosity.get() == 0) return;
  std::cout << "c     bounds ";
  if (solver.foundSolution()) {
    std::cout << upper_bound;
  } else {
    std::cout << "-";
  }
  std::cout << " >= " << lower_bound << " @ " << ilp.stats.getTime() << "\n";
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::checkLazyVariables() {
  // TODO: take *upper* bound on reformed objective into account.
  // E.g.: objective x+y+z+w =< 3 for core x+y+z+w >= 1 means we can rewrite to x+y+z+w = 1+a+b instead of = 1+a+b+c
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    LazyVar<SMALL, LARGE>& lv = *lazyVars[i];
    if (reformObj->getLit(lv.currentVar) == 0) {
      lv.setUpperBound(normalizedUpperBound());
      if (lv.remainingVars() == 0 ||
          isUnit(solver.getLevel(), -lv.currentVar)) {  // binary constraints make all new auxiliary variables unit
        lv.addFinalAtMost();
        aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
      } else {                          // add auxiliary variable
        int newN = solver.getNbVars() + 1;
        solver.setNbVars(newN, false);
        Var oldvar = lv.currentVar;
        lv.addVar(newN);
        // reformulate the objective
        reformObj->addLhs(lv.mult, newN);
        // add necessary lazy constraints
        lv.addAtLeastConstraint();
        lv.addAtMostConstraint();
        lv.addSymBreakingConstraint(oldvar);
        if (lv.remainingVars() == 0) {
          aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
        }
      }
    }
  }
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::addLowerBound() {
  CePtr<SMALL, LARGE> aux = ilp.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->addRhs(lower_bound);
  solver.dropExternal(lastLowerBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::LOWERBOUND);
  lastLowerBoundUnprocessed = res.first;
  lastLowerBound = res.second;
  if (lastLowerBound == ID_Unsat) return State::UNSAT;
  if (harden() == State::UNSAT) return State::UNSAT;
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
Ce32 Optimization<SMALL, LARGE>::reduceToCardinality(const CeSuper& core) {  // does not modify core
  CeSuper card = core->clone(ilp.cePools);
  CeSuper cloneCoefOrder = card->clone(ilp.cePools);
  cloneCoefOrder->sortInDecreasingCoefOrder(solver.getHeuristic());
  cloneCoefOrder->reverseOrder();  // *IN*creasing coef order
  card->sortWithCoefTiebreaker(
      [&](Var v1, Var v2) { return aux::sgn(aux::abs(reformObj->coefs[v1]) - aux::abs(reformObj->coefs[v2])); });

  CeSuper clone = card->clone(ilp.cePools);
  assert(clone->nVars() > 0);
  LARGE bestLowerBound = 0;
  int bestNbVars = clone->nVars();
  int bestCardDegree = 0;

  // find the optimum number of variables to weaken to
  while (!clone->isTautology()) {
    int carddegree = cloneCoefOrder->getCardinalityDegreeWithZeroes();
    SMALL currentObjCoef = aux::abs(reformObj->coefs[clone->getVars().back()]);
    LARGE lb = currentObjCoef * carddegree;
    if (bestLowerBound < lb) {
      bestLowerBound = lb;
      bestNbVars = clone->nVars();
      bestCardDegree = carddegree;
    }
    // weaken all lowest objective coefficient literals
    while (clone->nVars() > 0 && currentObjCoef == aux::abs(reformObj->coefs[clone->getVars().back()])) {
      cloneCoefOrder->weaken(clone->getVars().back());
      clone->weakenLast();
    }
  }

  // weaken to the optimum number of variables and generate cardinality constraint
  while ((int)card->nVars() > bestNbVars) {
    card->weakenLast();
  }
  // sort in decreasing coef order to minimize number of auxiliary variables, but break ties so that *large*
  // objective coefficient literals are removed first, as the smallest objective coefficients are the ones that
  // will be eliminated from the objective function. Thanks Stephan!
  card->sortInDecreasingCoefOrder(
      [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) < aux::abs(reformObj->coefs[v2]); });
  assert(bestCardDegree == card->getCardinalityDegree());
  card->simplifyToCardinality(false, bestCardDegree);

  Ce32 result = ilp.cePools.take32();
  card->copyTo(result);
  return result;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::reformObjectiveLog(const CeSuper& core) {
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  aux::predicate<Lit> toWeaken = [&](Lit l) { return !reformObj->hasLit(l); };
  if (!core->isSaturated(toWeaken)) {
    core->weaken(toWeaken);
    core->removeZeroes();
  }
  core->saturate(true, false);
  if (core->isTautology()) {
    return State::FAIL;
  }
  // the following operations do not turn core/reduced into a tautology
  core->divideTo(limitAbs<int, long long>(), [&](Lit l) { return reformObj->hasLit(l); });
  assert(!core->isTautology());
  CePtr<SMALL, LARGE> reduced = ilp.cePools.take<SMALL, LARGE>();
  core->copyTo(reduced);

  // decide rational multiplier using knapsack heuristic

  Lit cutoff = getKnapsackLit(reduced);
  LARGE div = reduced->getCoef(cutoff);
  assert(div > 0);
  SMALL mult = reformObj->getCoef(cutoff);
  assert(mult > 0);
  reduced->multiply(mult);
  reduced->weakenDivideRound(
      div, [&](Lit l) { return reformObj->hasLit(l) && reformObj->getCoef(l) * div >= reduced->getCoef(l); }, 0);
  // weaken all literals with a lower objective to reduced coefficient ratio than the ith literal in reduced
  // TODO: sorted?

  // create extended lower bound
  LARGE range = reduced->absCoeffSum() - reduced->getDegree();
  assert(range > 0);
  int newvars = aux::msb(range) + 1;
  assert((limitBit<SMALL, LARGE>()) >= newvars);
  int oldvars = solver.getNbVars();
  solver.setNbVars(oldvars + newvars, false);
  SMALL base = 1;
  for (Var var = oldvars + 1; var <= solver.getNbVars(); ++var) {
    reduced->addLhs(-base, var);
    range -= base;
    base *= 2;
    if (base > range) {
      base = static_cast<SMALL>(range);
    }
  }
  assert(range == 0);

  // add extended lower bound as constraint
  solver.addConstraintUnchecked(reduced, Origin::COREGUIDED);

  // add other side of equality as constraint
  reduced->invert();
  solver.addConstraintUnchecked(reduced, Origin::COREGUIDED);

  // add to objective
  reformObj->addUp(reduced);
  lower_bound = -reformObj->getDegree();

  // wrap up
  if (addLowerBound() == State::UNSAT) return State::UNSAT;

  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
Lit Optimization<SMALL, LARGE>::getKnapsackLit(const CePtr<SMALL, LARGE>& core) const {
  core->sortWithCoefTiebreaker([&](Var v1, Var v2) {
    const LARGE o1r2 = reformObj->getLit(v1) == core->getLit(v1) ? aux::abs(reformObj->coefs[v1] * core->coefs[v2]) : 0;
    const LARGE o2r1 = reformObj->getLit(v2) == core->getLit(v2) ? aux::abs(reformObj->coefs[v2] * core->coefs[v1]) : 0;
    return aux::sgn(o1r2 - o2r1);
    // TODO: check whether sorting the literals is a bottleneck
    // TODO: cast to LARGE when using smaller SMALL, LARGE
  });
  LARGE range = core->getDegree();
  int i = core->nVars();
  while (range >= 0 && i > 0) {
    --i;
    range -= core->nthCoef(i);
  }
  ++i;
  assert(i <= core->nVars());
  assert(i >= 0);
  return core->getLit(core->vars[i]);
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::reformObjectiveSmallSum(const CeSuper& core) {
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  aux::predicate<Lit> toWeaken = [&](Lit l) { return !reformObj->hasLit(l); };
  if (!core->isSaturated(toWeaken)) {
    core->weaken(toWeaken);
    core->removeZeroes();
  }
  core->saturate(true, false);
  if (core->isTautology()) {
    return State::FAIL;
  }
  CeSuper clone = core->clone(ilp.cePools);
  // the following operations do not turn core/reduced into a tautology
  SMALL largestCoef = 0;
  for (Var v : core->getVars()) {
    largestCoef = std::max(largestCoef, reformObj->getCoef(core->getLit(v)));
  }
  assert(largestCoef > 0);
  int maxCoef = static_cast<int>(std::min(largestCoef, static_cast<SMALL>(ilp.options.cgMaxCoef.get())));
  maxCoef = std::min(maxCoef, static_cast<int>(limitAbs<int, long long>()) / core->nVars());
  assert(maxCoef >= 1);
  if (maxCoef == 1) return reformObjective(core);

  core->divideTo(maxCoef, [&](Lit l) { return reformObj->hasLit(l); });
  assert(!core->isTautology());
  CePtr<SMALL, LARGE> reduced = ilp.cePools.take<SMALL, LARGE>();
  core->copyTo(reduced);

  // decide rational multiplier using knapsack heuristic
  Lit cutoff = getKnapsackLit(reduced);
  // ensure sum of coefficients fits in int
  LARGE div = reduced->getCoef(cutoff);
  assert(div > 0);
  SMALL mult = reformObj->getCoef(cutoff);
  assert(mult > 0);
  if (div > mult) {
    reduced->multiply(mult);
    // weaken all literals with a lower objective to reduced coefficient ratio than the ith literal in reduced
    // TODO: sorted?
    reduced->weakenDivideRound(
        div, [&](Lit l) { return reformObj->hasLit(l) && reformObj->getCoef(l) * div >= reduced->getCoef(l); }, 0);
    mult = 1;
  } else {
    mult /= static_cast<SMALL>(div);
  }
  assert(reduced->getLargestCoef() <= ilp.options.cgMaxCoef.get());
  assert(reduced->getDegree() > 0);
  assert(reduced->absCoeffSum() - reduced->getDegree() >= 0);
  assert(reduced->absCoeffSum() - reduced->getDegree() > 0);  // TODO: if it is 0, we have a unit constraint!
  assert(reduced->absCoeffSum() - reduced->getDegree() < INF - solver.getNbVars());
  Ce32 cardCore = ilp.cePools.take32();
  reduced->copyTo(cardCore);  // TODO: simply work in Ce32?
  reduced->multiply(mult);

  // TODO: don't add LazyVar when only 1 auxiliary variable is needed.
  // add auxiliary variable
  int newN = solver.getNbVars() + 1;
  solver.setNbVars(newN, false);
  // reformulate the objective
  reduced->invert();
  reformObj->addUp(reduced);
  reformObj->addLhs(mult, newN);  // add only one variable for now
  reduced->invert();
  LARGE exceedSum = reformObj->getDegree() + lower_bound + reduced->getDegree();
  lower_bound = -reformObj->getDegree();
  // add first lazy constraint
  lazyVars.push_back(
      std::make_unique<LazyVar<SMALL, LARGE>>(solver, cardCore, newN, mult, exceedSum, normalizedUpperBound()));
  lazyVars.back()->addAtLeastConstraint();
  lazyVars.back()->addAtMostConstraint();
  if (addLowerBound() == State::UNSAT) return State::UNSAT;

  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::reformObjective(const CeSuper& core) {  // modifies core
  assert(core->hasNegativeSlack(solver.getAssumptions().getIndex()));
  core->weaken([&](Lit l) { return !solver.getAssumptions().has(-l) || !reformObj->hasLit(l); });
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  core->saturate(true, false);
  if (!core->hasNegativeSlack(solver.getAssumptions().getIndex())) {
    return State::FAIL;
  }
  Ce32 cardCore = reduceToCardinality(core);
  assert(cardCore->hasNegativeSlack(solver.getAssumptions().getIndex()));
  assert(cardCore->hasNoZeroes());
  ilp.stats.NCGNONCLAUSALCORES += !cardCore->isClause();

  // adjust the lower bound
  assert(cardCore->nVars() > 0);
  SMALL mult = 0;
  for (Var v : cardCore->getVars()) {
    assert(reformObj->getLit(v) != 0);
    if (mult == 0) {
      mult = aux::abs(reformObj->coefs[v]);
    } else if (mult == 1) {
      break;
    } else {
      mult = std::min(mult, aux::abs(reformObj->coefs[v]));
    }
  }
  assert(mult > 0);
  lower_bound += cardCore->getDegree() * static_cast<LARGE>(mult);

  // add auxiliary variable
  int newN = solver.getNbVars() + 1;
  solver.setNbVars(newN, false);
  // reformulate the objective
  cardCore->invert();
  reformObj->addUp(cardCore, mult);
  cardCore->invert();
  reformObj->addLhs(mult, newN);  // add only one variable for now
  assert(lower_bound == -reformObj->getDegree());
  // add first lazy constraint
  lazyVars.push_back(std::make_unique<LazyVar<SMALL, LARGE>>(solver, cardCore, newN, mult, 0, normalizedUpperBound()));
  lazyVars.back()->addAtLeastConstraint();
  lazyVars.back()->addAtMostConstraint();
  if (addLowerBound() == State::UNSAT) return State::UNSAT;
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::handleInconsistency(const CeSuper& core) {  // modifies core
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  [[maybe_unused]] LARGE prev_lower = lower_bound;
  lower_bound = -reformObj->getDegree();

  if (core) {
    core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    core->saturate(true, false);
  }
  if (!core || core->isTautology()) {
    // only violated unit assumptions were derived
    assert(solver.assumptionsClashWithUnits());
    ++ilp.stats.NCGUNITCORES;
    assert(lower_bound > prev_lower);
    if (addLowerBound() == State::UNSAT) return State::UNSAT;
    checkLazyVariables();
    return State::SUCCESS;
  }
  assert(!core->hasNegativeSlack(solver.getLevel()));  // Would be handled by solver's learnConstraint
  --ilp.stats.NCGCOREREUSES;
  State result = State::SUCCESS;
  if (ilp.options.cgEncoding.is("binary")) {
    while (result == State::SUCCESS) {
      ++ilp.stats.NCGCOREREUSES;
      result = reformObjectiveLog(core);
    }
  } else if (ilp.options.cgEncoding.is("smallsum")) {
    while (result == State::SUCCESS) {
      ++ilp.stats.NCGCOREREUSES;
      result = reformObjectiveSmallSum(core);
    }
  } else {
    while (result == State::SUCCESS) {
      ++ilp.stats.NCGCOREREUSES;
      result = reformObjective(core);
    }
  }
  if (ilp.stats.DEPLTIME.z == -1 &&
      std::none_of(reformObj->getVars().begin(), reformObj->getVars().end(), [&](Var v) { return solver.isOrig(v); })) {
    ilp.stats.DEPLTIME.z = ilp.stats.getTime();
  }

  if (result == State::UNSAT) return State::UNSAT;

  checkLazyVariables();
  printObjBounds();
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::handleNewSolution(const std::vector<Lit>& sol) {
  assert(solver.checkSAT(sol));
  [[maybe_unused]] LARGE prev_val = upper_bound;
  upper_bound = -origObj->getRhs();
  for (Var v : origObj->getVars()) upper_bound += origObj->coefs[v] * (int)(sol[v] > 0);
  assert(upper_bound <= prev_val);
  assert(upper_bound < prev_val || !ilp.options.boundUpper);

  CePtr<SMALL, LARGE> aux = ilp.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::UPPERBOUND);
  lastUpperBoundUnprocessed = res.first;
  lastUpperBound = res.second;
  if (lastUpperBound == ID_Unsat) return State::UNSAT;
  if (harden() == State::UNSAT) return State::UNSAT;

  printObjBounds();
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::logProof() {
  if (!ilp.logger.isActive()) return;
  assert(lastUpperBound != ID_Undef);
  assert(lastUpperBound != ID_Unsat);
  assert(lastLowerBound != ID_Undef);
  assert(lastLowerBound != ID_Unsat);
  CePtr<SMALL, LARGE> coreAggregate = ilp.cePools.take<SMALL, LARGE>();
  CePtr<SMALL, LARGE> aux = ilp.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(1 - upper_bound);
  aux->resetBuffer(lastUpperBoundUnprocessed);
  coreAggregate->addUp(aux);
  aux->reset(false);
  origObj->copyTo(aux);
  aux->addRhs(lower_bound);
  aux->resetBuffer(lastLowerBoundUnprocessed);
  coreAggregate->addUp(aux);
  assert(coreAggregate->hasNegativeSlack(solver.getLevel()));
  assert(solver.decisionLevel() == 0);
  ilp.logger.logInconsistency(coreAggregate, solver.getLevel(), solver.getPos());
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::harden() {
  LARGE diff = upper_bound - lower_bound;
  for (Var v : reformObj->getVars()) {
    if (aux::abs(reformObj->coefs[v]) > diff) {
      if (solver.addUnitConstraint(-reformObj->getLit(v), Origin::HARDENEDBOUND) == ID_Unsat) {
        return State::UNSAT;
      }
    }
  }
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::runTabu() {
  if (ilp.options.verbosity.get() > 1) std::cout << "RUNNING TABU" << std::endl;
  int currentUnits = solver.getNbUnits();
  solver.phaseToTabu();
  bool success = false;
  while (solver.runTabuOnce()) {
    assert(solver.getTabuViolatedSize() == 0);
    success = true;
    ++ilp.stats.TABUSOLS;
    ++solutionsFound;
    if (ilp.options.boundUpper && handleNewSolution(solver.getLastSolution()) == State::UNSAT) return State::UNSAT;
    // NOTE: may flip tabuSol due to unit propagations
    // TODO: return SAT state to python interface...
  }
  if (success) solver.lastSolToPhase();
  // if (firstRun && ilp.options.varInitAct) solver.ranksToAct(); // TODO: check refactor of firstRun
  ilp.stats.NTABUUNITS += solver.getNbUnits() - currentUnits;
  if (ilp.options.verbosity.get() > 0) std::cout << "c END LOCAL SEARCH" << std::endl;

  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::optimize(const std::vector<Lit>& assumptions) {
  if (firstRun) {
    firstRun = false;
    std::pair<State, CeSuper> res = solver.presolve();
    if (res.first == State::UNSAT) return SolveState::UNSAT;
  }

  while (true) {
    assert(upper_bound >= lower_bound);
    StatNum current_time = ilp.stats.getDetTime();
    if (reply == SolveState::INPROCESSED) {
      if (ilp.options.printCsvData)
        ilp.stats.printCsvLine(static_cast<StatNum>(lower_bound), static_cast<StatNum>(upper_bound));
      if (ilp.options.tabuLim.get() != 0) {
        State state = aux::timeCall<State>([&] { return runTabu(); }, ilp.stats.TABUTIME);
        if (state == State::UNSAT) return SolveState::UNSAT;
      }
    }
    if (lower_bound >= upper_bound && ilp.options.boundUpper) {
      logProof();
      return SolveState::UNSAT;  // optimality is proven
    }

    if (assumptions.empty() && coreguided) {
      while (!solver.hasAssumptions()) {
        reformObj->removeEqualities(solver.getEqualities(), false);
        reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
        if (ilp.stats.DEPLTIME.z == -1 && std::none_of(reformObj->getVars().begin(), reformObj->getVars().end(),
                                                       [&](Var v) { return solver.isOrig(v); })) {
          ilp.stats.DEPLTIME.z = ilp.stats.getTime();
        }
        std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than bigint
        litcoefs.reserve(reformObj->nVars());
        if (!ilp.options.cgReform.is("always")) {
          for (Var v : reformObj->getVars()) {
            assert(reformObj->getLit(v) != 0);
            if (!solver.isOrig(v)) continue;
            double cf = aux::abs(aux::toDouble(reformObj->coefs[v]));
            if (cf >= stratLim) {
              litcoefs.emplace_back(cf, v);
            }
          }
        }
        if ((ilp.options.cgReform.is("depletion") && litcoefs.empty()) || ilp.options.cgReform.is("always")) {
          for (Var v : reformObj->getVars()) {
            assert(reformObj->getLit(v) != 0);
            double cf = aux::abs(aux::toDouble(reformObj->coefs[v]));
            if (cf >= stratLim) {
              litcoefs.emplace_back(cf, v);
            }
          }
        }
        std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double>& t1, const Term<double>& t2) {
          return t1.c > t2.c || (t1.l < t2.l && t1.c == t2.c);
        });
        std::vector<Lit> assumps;
        assumps.reserve(litcoefs.size());
        for (const Term<double>& t : litcoefs) assumps.push_back(-reformObj->getLit(toVar(t.l)));
        solver.setAssumptions(assumps);
        if (assumps.size() == 0) break;
        if (solver.lastGlobalDual && solver.lastGlobalDual->hasNegativeSlack(solver.getAssumptions().getIndex())) {
          if (handleInconsistency(solver.lastGlobalDual) == State::UNSAT) return SolveState::UNSAT;
          solver.clearAssumptions();
        }
      }
    } else {
      solver.setAssumptions(assumptions);
    }

    reply = aux::timeCall<SolveState>([&] { return solver.solve(); },
                                      solver.hasAssumptions() ? ilp.stats.SOLVETIMEASSUMP : ilp.stats.SOLVETIMEFREE);

    if (solver.hasAssumptions()) {
      ilp.stats.DETTIMEASSUMP += ilp.stats.getDetTime() - current_time;
    } else {
      ilp.stats.DETTIMEFREE += ilp.stats.getDetTime() - current_time;
    }
    if (reply == SolveState::UNSAT) {
      return SolveState::UNSAT;
    } else if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++ilp.stats.NSOLS;
      ++solutionsFound;
      if (ilp.options.boundUpper && handleNewSolution(solver.getLastSolution()) == State::UNSAT)
        return SolveState::UNSAT;
      if (coreguided) {
        solver.clearAssumptions();
        stratLim = std::max<double>(stratLim / stratDiv, 1);
      }
      somethingHappened = true;
      return SolveState::SAT;
    } else if (reply == SolveState::INCONSISTENT) {
      ++ilp.stats.NCORES;
      somethingHappened = true;
      if (!assumptions.empty()) return SolveState::INCONSISTENT;
      assert(coreguided);  // else: core from core-guided search
      if (handleInconsistency(solver.lastCore) == State::UNSAT) return SolveState::UNSAT;
      solver.clearAssumptions();
    } else if (reply == SolveState::INPROCESSED) {
      // NOTE: returning when inprocessing avoids long non-terminating solve calls
      if (!somethingHappened && coreguided) {
        solver.clearAssumptions();
        stratLim = std::max<double>(stratLim / stratDiv, 1);
      }
      somethingHappened = false;
      coreguided =
          ilp.options.cgHybrid.get() >= 1 ||
          ilp.stats.DETTIMEASSUMP < ilp.options.cgHybrid.get() * (ilp.stats.DETTIMEFREE + ilp.stats.DETTIMEASSUMP);
      return SolveState::INPROCESSED;
    } else {
      assert(false);  // should not happen
    }
  }
}

template class Optimization<int, long long>;
template class Optimization<long long, int128>;
template class Optimization<int128, int128>;
template class Optimization<int128, int256>;
template class Optimization<bigint, bigint>;

template class LazyVar<int, long long>;
template class LazyVar<long long, int128>;
template class LazyVar<int128, int128>;
template class LazyVar<int128, int256>;
template class LazyVar<bigint, bigint>;

}  // namespace xct
