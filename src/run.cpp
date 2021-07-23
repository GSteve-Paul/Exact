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

#include "run.hpp"
#include "ConstrExp.hpp"
#include "Solver.hpp"

namespace rs::run {

Solver solver;

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
    Term<int>& last = atLeast.terms.back();
    last = {last.c - 1, v};
    --atMost.rhs;
    Term<int>& last2 = atMost.terms.back();
    last2 = {remainingVars(), v};
  } else {
    atLeast.terms.emplace_back(-1, v);
    Term<int>& last = atMost.terms.back();
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
  Term<int>& last = atMost.terms.back();
  last = {1, last.l};
  solver.addConstraintUnchecked(atMost, Origin::COREGUIDED);
}

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar>& lv) {
  o << lv->atLeast << "\n" << lv->atMost;
  return o;
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(CePtr<ConstrExp<SMALL, LARGE>> obj) : origObj(obj) {
  // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  lower_bound = -origObj->getDegree();
  upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

  reformObj = cePools.take<SMALL, LARGE>();
  reformObj->stopLogging();
  origObj->copyTo(reformObj);
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
State Optimization<SMALL, LARGE>::reformObjective(const CeSuper& core) {  // modifies core
  Ce32 cardCore = reduceToCardinality(core);
  assert(cardCore->hasNegativeSlack(solver.getAssumptions()));
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

  for (Var v : core->getVars()) {
    if (reformObj->coefs[v] == 0) {
      core->weaken(v);
    } else {
      assert(reformObj->getLit(v) == core->getLit(v));
    }
  }
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  core->saturate(true, false);
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
  assert(!core->hasNegativeSlack(solver.getLevel()));  // Would be handled by Solver's learnConstraint
  --stats.NCGCOREREUSES;
  while (!core->isTautology()) {
    ++stats.NCGCOREREUSES;
    if (reformObjective(core) == State::UNSAT) return State::UNSAT;
  }
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
  assert(upper_bound < prev_val || options.enumerateSolutions());
  solver.bestObjSoFar = upper_bound;
  ++solutionsFound;

  if (!solver.hasObjective() && options.enumerateSolutions()) {
    if (options.verbosity.get() > 0) {
      std::cout << "c solution " << solutionsFound << std::endl;
    }
    quit::printLits(sol, 'v', true);
    ConstrSimple32 invalidator;
    invalidator.terms.reserve(solver.getNbOrigVars() + 1);
    invalidator.rhs = 1;
    for (Lit l : sol) {
      if (l == 0 || toVar(l) > solver.getNbOrigVars()) continue;
      invalidator.terms.push_back({1, -l});
    }
    std::pair<ID, ID> res = solver.addConstraint(invalidator, Origin::INVALIDATOR);
    if (res.second == ID_Unsat) return State::UNSAT;
  } else {
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
  }
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
    if (handleNewSolution(solver.getLastSolution()) == State::UNSAT) return State::UNSAT;
    // NOTE: may flip tabuSol due to unit propagations
  }
  if (success) solver.lastSolToPhase();
  stats.NTABUUNITS += solver.getNbUnits() - currentUnits;
  if (options.verbosity.get() > 0) std::cout << "c END LOCAL SEARCH" << std::endl;
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
State Optimization<SMALL, LARGE>::optimize() {
  SolveState reply = SolveState::SAT;
  float stratDiv = options.cgStrat.get();
  double stratLim = stratDiv == 1 ? 1 : aux::toDouble(reformObj->getLargestCoef());
  bool coreguided = options.cgHybrid.get() >= 1;
  bool somethingHappened = false;
  if (options.tabuLim.get() != 0) {
    State state = aux::timeCall<State>([&] { return runTabu(); }, stats.TABUTIME);
    if (state == State::UNSAT) return State::UNSAT;
  }
  if (options.varInitAct) solver.ranksToAct();
  while (true) {
    long double current_time = stats.getDetTime();
    if (reply == SolveState::INPROCESSED && options.printCsvData) stats.printCsvLine();

    if (coreguided) {
      if (!solver.hasAssumptions()) {
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
      if (solver.hasAssumptions()) {
        solver.clearAssumptions();
      }
    }
    assert(upper_bound >= lower_bound);
    assert(upper_bound > lower_bound || options.enumerateSolutions());

    reply = aux::timeCall<SolveState>([&] { return solver.solve(); },
                                      solver.hasAssumptions() ? stats.SOLVETIMEASSUMP : stats.SOLVETIMEFREE);
    if (solver.hasAssumptions()) {
      stats.DETTIMEASSUMP += stats.getDetTime() - current_time;
    } else {
      stats.DETTIMEFREE += stats.getDetTime() - current_time;
    }
    if (reply == SolveState::UNSAT) {
      return State::UNSAT;
    } else if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++stats.NSOLS;
      if (handleNewSolution(solver.getLastSolution()) == State::UNSAT) return State::UNSAT;
      if (coreguided) {
        solver.clearAssumptions();
        stratLim = std::max<double>(stratLim / stratDiv, 1);
      }
      somethingHappened = true;
    } else if (reply == SolveState::INCONSISTENT) {
      ++stats.NCORES;
      if (handleInconsistency(solver.lastCore) == State::UNSAT) return State::UNSAT;
      solver.clearAssumptions();
      somethingHappened = true;
    } else if (reply == SolveState::INPROCESSED) {
      // NOTE: returning when inprocessing avoids long non-terminating solve calls
      if (!somethingHappened && coreguided) {
        solver.clearAssumptions();
        stratLim = std::max<double>(stratLim / stratDiv, 1);
      }
      somethingHappened = false;
      coreguided = options.cgHybrid.get() >= 1 ||
                   stats.DETTIMEASSUMP < options.cgHybrid.get() * (stats.DETTIMEFREE + stats.DETTIMEASSUMP);

      if (options.tabuLim.get() != 0) {
        State state = aux::timeCall<State>([&] { return runTabu(); }, stats.TABUTIME);
        if (state == State::UNSAT) return State::UNSAT;
      }
    } else {
      assert(false);  // should not happen
    }
    if (lower_bound >= upper_bound && options.enumerate.get() != 0 && solutionsFound >= options.enumerate.get()) {
      logProof();
      return State::SUCCESS;
    }
  }
}

template class Optimization<int, long long>;
template class Optimization<long long, int128>;
template class Optimization<int128, int128>;
template class Optimization<int128, int256>;
template class Optimization<bigint, bigint>;

void run() {
  if (options.noSolve) quit::exit_INDETERMINATE(solver);

  stats.RUNSTARTTIME.z = aux::cpuTime();
  if (options.printCsvData) {
    stats.printCsvHeader();
  }
  if (options.verbosity.get() > 0) {
    std::cout << "c " << solver.getNbOrigVars() << " vars " << solver.getNbConstraints() << " constrs" << std::endl;
  }
  try {
    solver.objective->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    bigint maxVal = solver.objective->getCutoffVal();
    if (maxVal <= limit32) {  // TODO: try to internalize this check in ConstrExp
      runOptimize(cePools.take32());
    } else if (maxVal <= limit64) {
      runOptimize(cePools.take64());
    } else if (maxVal <= static_cast<bigint>(limit96)) {
      runOptimize(cePools.take96());
    } else if (maxVal <= static_cast<bigint>(limit128)) {
      runOptimize(cePools.take128());
    } else {
      runOptimize(cePools.takeArb());
    }
  } catch (const AsynchronousInterrupt& ai) {
    if (options.outputMode.is("default")) {
      std::cout << "c " << ai.what() << std::endl;
    }
    quit::exit_INDETERMINATE(solver);
  }
}

}  // namespace rs::run
