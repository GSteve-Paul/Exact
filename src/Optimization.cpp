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

LazyVar::LazyVar(Solver& slvr, const Ce32& cardCore, int cardUpperBound, Var startVar)
    : solver(slvr), coveredVars(cardCore->getDegree()), upperBound(cardUpperBound) {
  assert(cardCore->isCardinality());
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

LazyVar::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

int LazyVar::remainingVars() const { return upperBound - coveredVars; }

void LazyVar::setUpperBound(int cardUpperBound) {
  assert(upperBound >= cardUpperBound);
  upperBound = cardUpperBound;
}

void LazyVar::addVar(Var v, bool reified) {
  currentVar = v;
  if (reified) {
    Term32& last = atLeast.terms.back();
    last = {last.c - 1, v};
    --atMost.rhs;
    Term32& last2 = atMost.terms.back();
    last2 = {remainingVars(), v};
  } else {
    atLeast.terms.emplace_back(-1, v);
    Term32& last = atMost.terms.back();
    last = {1, last.l};
    atMost.terms.emplace_back(remainingVars(), v);
  }
  ++coveredVars;
}

void LazyVar::addAtLeastConstraint(bool reified) {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, !reified, false);  // TODO: should non-reified constraints be force deleted?
  solver.addConstraintUnchecked(atLeast, Origin::COREGUIDED);
}

void LazyVar::addAtMostConstraint(bool reified) {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, !reified, false);
  solver.addConstraintUnchecked(atMost, Origin::COREGUIDED);
}

void LazyVar::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  solver.addConstraintUnchecked(ConstrSimple32({{1, prevvar}, {1, -currentVar}}, 1), Origin::COREGUIDED);
}

void LazyVar::addFinalAtMost(bool reified) {
  solver.dropExternal(atMostID, !reified, false);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  solver.addConstraintUnchecked(atMost, Origin::COREGUIDED);
}

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar>& lv) {
  o << lv->atLeast << "\n" << lv->atMost;
  return o;
}

OptimizationSuper::OptimizationSuper(Solver& s) : solver(s) {}

Optim OptimizationSuper::make(const CeArb& obj, Solver& solver) {
  bigint maxVal = obj->getCutoffVal() * INF;  // INF factor allows adding log-encoded core to the objective
  if (maxVal <= static_cast<bigint>(limitAbs<int, long long>())) {  // TODO: try to internalize this check in ConstrExp
    Ce32 o = cePools.take32();
    obj->copyTo(o);
    return std::make_shared<Optimization<int, long long>>(o, solver);
  } else if (maxVal <= static_cast<bigint>(limitAbs<long long, int128>())) {
    Ce64 o = cePools.take64();
    obj->copyTo(o);
    return std::make_shared<Optimization<long long, int128>>(o, solver);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int128>())) {
    Ce96 o = cePools.take96();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int128>>(o, solver);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int256>())) {
    Ce128 o = cePools.take128();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int256>>(o, solver);
  } else {
    CeArb o = cePools.takeArb();
    obj->copyTo(o);
    return std::make_shared<Optimization<bigint, bigint>>(o, solver);
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(const CePtr<ConstrExp<SMALL, LARGE>>& obj, Solver& s)
    : OptimizationSuper(s), origObj(obj) {
  // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  lower_bound = -origObj->getDegree();
  upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

  reformObj = cePools.take<SMALL, LARGE>();
  reformObj->stopLogging();
  origObj->copyTo(reformObj);
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  reformObj->removeEqualities(solver.getEqualities(), false);

  reply = SolveState::INPROCESSED;
  stratDiv = options.cgStrat.get();
  stratLim = stratDiv == 1 ? 1 : aux::toDouble(reformObj->getLargestCoef());
  coreguided = options.cgHybrid.get() >= 1;
  somethingHappened = false;
  firstRun = true;
};

template <typename SMALL, typename LARGE>
CeSuper Optimization<SMALL, LARGE>::getReformObj() const {
  return reformObj;
};

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::printObjBounds() {
  if (options.verbosity.get() == 0) return;
  std::cout << "c     bounds ";
  if (solver.foundSolution()) {
    std::cout << upper_bound;
  } else {
    std::cout << "-";
  }
  std::cout << " >= " << lower_bound << " @ " << stats.getTime() << "\n";
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::checkLazyVariables() {
  bool reified = options.cgEncoding.is("reified");
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    LazyVar& lv = *lazyVars[i].lv;
    if (reformObj->getLit(lv.currentVar) == 0) {
      lv.setUpperBound(static_cast<int>(std::min<LARGE>(lv.upperBound, normalizedUpperBound() / lazyVars[i].m)));
      if (lv.remainingVars() == 0 ||
          isUnit(solver.getLevel(), -lv.currentVar)) {  // binary constraints make all new auxiliary variables unit
        lv.addFinalAtMost(reified);
        aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
      } else {                          // add auxiliary variable
        int newN = solver.getNbVars() + 1;
        solver.setNbVars(newN, false);
        Var oldvar = lv.currentVar;
        lv.addVar(newN, reified);
        // reformulate the objective
        reformObj->addLhs(lazyVars[i].m, newN);
        // add necessary lazy constraints
        lv.addAtLeastConstraint(reified);
        lv.addAtMostConstraint(reified);
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
  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
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
  CeSuper card = core->clone(cePools);
  CeSuper cloneCoefOrder = card->clone(cePools);
  cloneCoefOrder->sortInDecreasingCoefOrder(solver.getHeuristic());
  cloneCoefOrder->reverseOrder();  // *IN*creasing coef order
  card->sortWithCoefTiebreaker(
      [&](Var v1, Var v2) { return aux::sgn(aux::abs(reformObj->coefs[v1]) - aux::abs(reformObj->coefs[v2])); });

  CeSuper clone = card->clone(cePools);
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

  Ce32 result = cePools.take32();
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
  aux::predicate<Lit> falsified = [&](Lit l) { return reformObj->hasLit(l); };
  core->divideTo(limitAbs<int, long long>(), falsified);
  assert(!core->isTautology());
  CePtr<ConstrExp<SMALL, LARGE>> reduced = cePools.take<SMALL, LARGE>();
  core->copyTo(reduced);
  //  std::cout << core << std::endl;
  //  std::cout << reformObj << std::endl;

  //  reduced->reset(false);
  //  reduced->addLhs(1, 1);
  //  reduced->addLhs(2, 2);
  //  reduced->addLhs(2, 3);
  //  reduced->addLhs(3, 4);
  //  reduced->addLhs(3, 5);
  //  reduced->addRhs(options.test.get());
  //  reformObj->reset(false);
  //  reformObj->addLhs(2, 1);
  //  reformObj->addLhs(3, 2);
  //  reformObj->addLhs(4, 3);
  //  reformObj->addLhs(4, 4);
  //  reformObj->addLhs(5, 5);
  //  solver.setAssumptions({-1, -2, -3, -4, -5});

  // decide rational multiplier using knapsack heuristic
  reduced->sortWithCoefTiebreaker([&](Var v1, Var v2) {
    const LARGE o1r2 =
        reformObj->getLit(v1) == reduced->getLit(v1) ? aux::abs(reformObj->coefs[v1] * reduced->coefs[v2]) : 0;
    const LARGE o2r1 =
        reformObj->getLit(v2) == reduced->getLit(v2) ? aux::abs(reformObj->coefs[v2] * reduced->coefs[v1]) : 0;
    return aux::sgn(o1r2 - o2r1);
    // TODO: check whether sorting the literals is a bottleneck
    // TODO: cast to LARGE when using smaller SMALL, LARGE
  });
  LARGE range = reduced->getDegree();
  int i = reduced->nVars();
  while (range >= 0 && i > 0) {
    --i;
    range -= reduced->nthCoef(i);
  }
  ++i;
  assert(i <= reduced->nVars());
  LARGE div = reduced->nthCoef(i);
  SMALL mult = reformObj->getCoef(reduced->getLit(reduced->vars[i]));
  assert(mult > 0);
  reduced->multiply(mult);
  reduced->weakenDivideRound(div, falsified, 0);  // TODO: sorted?

  // create extended lower bound
  range = reduced->absCoeffSum() - reduced->getDegree();
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
  stats.NCGNONCLAUSALCORES += !cardCore->isClause();

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

  int cardCoreUpper = static_cast<int>(std::min<LARGE>(cardCore->nVars(), normalizedUpperBound() / mult));
  if (options.cgEncoding.is("sum") || cardCore->nVars() - cardCore->getDegree() <= 1) {
    // add auxiliary variables
    int oldN = solver.getNbVars();
    int newN = oldN - static_cast<int>(cardCore->getDegree()) + cardCoreUpper;
    assert(newN >= oldN);
    solver.setNbVars(newN, false);
    // reformulate the objective
    for (Var v = oldN + 1; v <= newN; ++v) cardCore->addLhs(-1, v);
    cardCore->invert();
    reformObj->addUp(cardCore, mult);
    assert(lower_bound == -reformObj->getDegree());
    // add channeling constraints
    solver.addConstraintUnchecked(cardCore, Origin::COREGUIDED);
    cardCore->invert();
    solver.addConstraintUnchecked(cardCore, Origin::COREGUIDED);
    for (Var v = oldN + 1; v < newN; ++v) {  // add symmetry breaking constraints
      solver.addConstraintUnchecked(ConstrSimple32({{1, v}, {1, -v - 1}}, 1), Origin::COREGUIDED);
    }
  } else {
    bool reified = options.cgEncoding.is("reified");
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
    lazyVars.push_back({std::make_unique<LazyVar>(solver, cardCore, cardCoreUpper, newN), mult});
    lazyVars.back().lv->addAtLeastConstraint(reified);
    lazyVars.back().lv->addAtMostConstraint(reified);
  }
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
    ++stats.NCGUNITCORES;
    assert(lower_bound > prev_lower);
    if (addLowerBound() == State::UNSAT) return State::UNSAT;
    checkLazyVariables();
    return State::SUCCESS;
  }
  assert(!core->hasNegativeSlack(solver.getLevel()));  // Would be handled by solver's learnConstraint
  --stats.NCGCOREREUSES;
  State result = State::SUCCESS;
  if (options.cgEncoding.is("log")) {
    while (result == State::SUCCESS) {
      ++stats.NCGCOREREUSES;
      result = reformObjectiveLog(core);
    }
  } else {
    while (result == State::SUCCESS) {
      ++stats.NCGCOREREUSES;
      result = reformObjective(core);
    }
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
  assert(upper_bound < prev_val || !options.boundUpper);

  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
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
  if (!logger) return;
  assert(lastUpperBound != ID_Undef);
  assert(lastUpperBound != ID_Unsat);
  assert(lastLowerBound != ID_Undef);
  assert(lastLowerBound != ID_Unsat);
  CePtr<ConstrExp<SMALL, LARGE>> coreAggregate = cePools.take<SMALL, LARGE>();
  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
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
  coreAggregate->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  logger->logInconsistency(coreAggregate);
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
  if (options.verbosity.get() > 1) std::cout << "RUNNING TABU" << std::endl;
  int currentUnits = solver.getNbUnits();
  solver.phaseToTabu();
  bool success = false;
  while (solver.runTabuOnce()) {
    assert(solver.getTabuViolatedSize() == 0);
    success = true;
    ++stats.TABUSOLS;
    ++solutionsFound;
    if (options.boundUpper && handleNewSolution(solver.getLastSolution()) == State::UNSAT) return State::UNSAT;
    // NOTE: may flip tabuSol due to unit propagations
    // TODO: return SAT state to python interface...
  }
  if (success) solver.lastSolToPhase();
  // if (firstRun && options.varInitAct) solver.ranksToAct(); // TODO: check refactor of firstRun
  stats.NTABUUNITS += solver.getNbUnits() - currentUnits;
  if (options.verbosity.get() > 0) std::cout << "c END LOCAL SEARCH" << std::endl;

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
    StatNum current_time = stats.getDetTime();
    if (reply == SolveState::INPROCESSED) {
      if (options.printCsvData) stats.printCsvLine();
      if (options.tabuLim.get() != 0) {
        State state = aux::timeCall<State>([&] { return runTabu(); }, stats.TABUTIME);
        if (state == State::UNSAT) return SolveState::UNSAT;
      }
    }
    if (lower_bound >= upper_bound && options.boundUpper) {
      logProof();
      return SolveState::UNSAT;  // optimality is proven
    }

    if (assumptions.empty() && coreguided) {
      if (!solver.hasAssumptions()) {
        reformObj->removeEqualities(solver.getEqualities(), false);
        reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
        std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than bigint
        litcoefs.reserve(reformObj->nVars());
        for (Var v : reformObj->getVars()) {
          assert(reformObj->getLit(v) != 0);
          double cf = aux::abs(aux::toDouble(reformObj->coefs[v]));
          if (cf >= stratLim) {
            litcoefs.emplace_back(cf, v);
          }
        }
        std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double>& t1, const Term<double>& t2) {
          return t1.c > t2.c || (t1.l < t2.l && t1.c == t2.c);
        });
        std::vector<Lit> assumps;
        assumps.reserve(litcoefs.size());
        for (const Term<double>& t : litcoefs) assumps.push_back(-reformObj->getLit(toVar(t.l)));
        solver.setAssumptions(assumps);
      }
    } else {
      solver.setAssumptions(assumptions);
    }

    reply = aux::timeCall<SolveState>([&] { return solver.solve(); },
                                      solver.hasAssumptions() ? stats.SOLVETIMEASSUMP : stats.SOLVETIMEFREE);

    if (solver.hasAssumptions()) {
      stats.DETTIMEASSUMP += stats.getDetTime() - current_time;
    } else {
      stats.DETTIMEFREE += stats.getDetTime() - current_time;
    }
    if (reply == SolveState::UNSAT) {
      return SolveState::UNSAT;
    } else if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++stats.NSOLS;
      ++solutionsFound;
      if (options.boundUpper && handleNewSolution(solver.getLastSolution()) == State::UNSAT) return SolveState::UNSAT;
      if (coreguided) {
        solver.clearAssumptions();
        stratLim = std::max<double>(stratLim / stratDiv, 1);
      }
      somethingHappened = true;
      return SolveState::SAT;
    } else if (reply == SolveState::INCONSISTENT) {
      ++stats.NCORES;
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
      coreguided = options.cgHybrid.get() >= 1 ||
                   stats.DETTIMEASSUMP < options.cgHybrid.get() * (stats.DETTIMEFREE + stats.DETTIMEASSUMP);
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

}  // namespace xct
