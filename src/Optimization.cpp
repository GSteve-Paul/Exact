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
#include "Global.hpp"
#include "ILP.hpp"
#include "Solver.hpp"
#include "constraints/ConstrExp.hpp"

namespace xct {

constexpr int stratFactor = 1000;

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::LazyVar(Solver& slvr, const Ce32& cardCore, Var startVar, const SMALL& m, int upperBnd)
    : solver(slvr), coveredVars(cardCore->getDegree()), upperBound(upperBnd), mult(m) {
  assert(remainingVars() > 0);
  cardCore->toSimple()->copyTo(atLeast);
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore->getDegree());
  atMost.rhs = -atLeast.rhs;
  atMost.terms.reserve(atLeast.size() + 1);
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
  upperBound = std::min(upperBound, static_cast<int>(normalizedUpperBound / mult));
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
  solver.addConstraint(atLeast, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addAtMostConstraint() {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, true, false);
  solver.addConstraint(atMost, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  solver.addBinaryConstraint(prevvar, -currentVar, Origin::COREGUIDED);
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addFinalAtMost() {
  solver.dropExternal(atMostID, true, false);
  Term32& last = atMost.terms.back();
  last = {1, last.l};
  solver.addConstraint(atMost, Origin::COREGUIDED);
}

OptimizationSuper::OptimizationSuper(Solver& s, const bigint& os, const IntSet& assumps)
    : solver(s), global(s.global), offset(os), assumptions(assumps) {}

Optim OptimizationSuper::make(const IntConstraint& ico, Solver& solver, const IntSet& assumps) {
  CeArb obj = solver.global.cePools.takeArb();
  ico.toConstrExp(obj, true);
  obj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  obj->removeEqualities(solver.getEqualities(), false);
  bigint offs = -obj->getDegree();
  obj->addRhs(offs);
  assert(obj->getDegree() == 0);
  solver.setObjective(obj);

  bigint maxVal = obj->absCoeffSum();
  // The argument that maxVal is a safe upper bound is that we may *increase* the coefficient of assumption literals
  // during core-based reformulation, but never higher than the original coefficient sum.
  // E.g., ax+by+cz
  // assuming q to false may yield the sequence of cores q+x>=1, q+y>=1, q+z>=1.
  // these will lead to the following reformulation equalities: x=u+~q, y=v+~q, z=w+~q.
  // with final reformulation (a+b+c)~q + au + bv + cz.
  // Sum of coefficients is a sensible upper bound, since the assumption of the corresponding literal to true would
  // mean that the objective is at its maximal value.
  //
  // Since q is assumed to false (user assumption) and auxiliaries u, v, w are assumed to false (reformulated objective
  // literals), the only cores that will increase q at the expense of u, v, w are those where both q and u, v, w are
  // positive. However, since q and u, v, w have opposed polarity in the reformulation equalities, no such cores exist.
  // Hence, q's coefficient will not be reformulated beyond the sum of coefficients.
  // TODO: get a more rigorous proof from this argument?

  if (maxVal <= static_cast<bigint>(limitAbs<int, long long>())) {  // TODO: try to internalize this check in ConstrExp
    Ce32 o = solver.global.cePools.take32();
    obj->copyTo(o);
    return std::make_unique<Optimization<int, long long>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<long long, int128>())) {
    Ce64 o = solver.global.cePools.take64();
    obj->copyTo(o);
    return std::make_unique<Optimization<long long, int128>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int128>())) {
    Ce96 o = solver.global.cePools.take96();
    obj->copyTo(o);
    return std::make_unique<Optimization<int128, int128>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int256>())) {
    Ce128 o = solver.global.cePools.take128();
    obj->copyTo(o);
    return std::make_unique<Optimization<int128, int256>>(o, solver, offs, assumps);
  } else {
    CeArb o = solver.global.cePools.takeArb();
    obj->copyTo(o);
    return std::make_unique<Optimization<bigint, bigint>>(o, solver, offs, assumps);
  }
}

template <typename SMALL, typename LARGE>
void simplifyAssumps(CePtr<SMALL, LARGE>& c, const IntSet& assumps) {
  for (const Lit l : assumps.getKeys()) {  // remove assumptions from objective
    const Var v = toVar(l);
    if (c->hasVar(v)) {
      if (c->hasLit(l)) c->addRhs(aux::abs(c->coefs[v]));
      c->coefs[v] = 0;
    }
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(const CePtr<SMALL, LARGE>& obj, Solver& s, const bigint& os,
                                         const IntSet& assumps)
    : OptimizationSuper(s, os, assumps),
      origObj(obj),
      reply(SolveState::INPROCESSED),
      stratDiv(stratFactor * global.options.cgStrat.get()),
      coreguided(global.options.cgHybrid.get() >= 1) {
  assert(origObj->getDegree() == 0);
  reformObj = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(reformObj);
  reformObj->removeEqualities(solver.getEqualities(), false);
  simplifyAssumps(reformObj, assumptions);
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());

  lower_bound = -reformObj->getDegree();
  upper_bound = origObj->absCoeffSum() + 1;
  stratLim = global.options.cgStrat.get() == 1 ? 1 : reformObj->getLargestCoef();
}

template <typename SMALL, typename LARGE>
bigint Optimization<SMALL, LARGE>::getUpperBound() const {
  return offset + upper_bound;
}
template <typename SMALL, typename LARGE>
bigint Optimization<SMALL, LARGE>::getLowerBound() const {
  return offset + lower_bound;
}
template <typename SMALL, typename LARGE>
CeSuper Optimization<SMALL, LARGE>::getOrigObj() const {
  return origObj;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::printObjBounds() {
  if (global.options.verbosity.get() == 0) return;
  std::cout << "c     bounds ";
  if (solver.foundSolution()) {
    std::cout << getUpperBound();
  } else {
    std::cout << "-";
  }
  std::cout << " >= " << getLowerBound() << " @ " << global.stats.getTime() << "\n";
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::checkLazyVariables() {
  // TODO: take *upper* bound on reformed objective into account.
  // E.g.: objective x+y+z+w =< 3 for core x+y+z+w >= 1 means we can rewrite to x+y+z+w = 1+a+b instead of = 1+a+b+c
  for (int i = 0; i < (int)lazyVars.size(); ++i) {
    LazyVar<SMALL, LARGE>& lv = *lazyVars[i];
    if (reformObj->getLit(lv.currentVar) == 0) {
      lv.setUpperBound(upper_bound);
      if (lv.remainingVars() == 0 ||
          isUnit(solver.getLevel(), -lv.currentVar)) {  // binary constraints make all new auxiliary variables unit
        lv.addFinalAtMost();
        plf::single_reorderase(lazyVars, lazyVars.begin() + i);  // fully expanded, no need to keep in memory
        --i;
      } else {  // add auxiliary variable
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
          plf::single_reorderase(lazyVars, lazyVars.begin() + i);  // fully expanded, no need to keep in memory
          --i;
        }
      }
    }
  }
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::addLowerBound() {
  if (!assumptions.isEmpty()) return;  // otherwise the lower_bound is not globally valid
  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->addRhs(lower_bound);
  solver.dropExternal(lastLowerBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::LOWERBOUND);
  lastLowerBound = res.second;
  harden();
}

template <typename SMALL, typename LARGE>
Ce32 Optimization<SMALL, LARGE>::reduceToCardinality(const CeSuper& core) {  // does not modify core
  assert(core->hasNoZeroes());
  assert(core->hasNoUnits(solver.getLevel()));
  if (core->isClause()) {
    Ce32 result = global.cePools.take32();
    core->copyTo(result);
    return result;
  }

  CeSuper card = core->clone(global.cePools);
  // sort in decreasing coef order to minimize number of auxiliary variables, but break ties so that *small*
  // objective coefficient literals are removed first, to maximize the chances of a strong lower bound.
  card->sortInDecreasingCoefOrder(
      [&](Var v1, Var v2) { return reformObj->getCoef(card->getLit(v1)) > reformObj->getCoef(card->getLit(v2)); });
  card->simplifyToCardinality(false, card->getCardinalityDegree());

  Ce32 result = global.cePools.take32();
  card->copyTo(result);
  return result;
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
State Optimization<SMALL, LARGE>::reformObjective(const CeSuper& core) {  // modifies core
  core->weaken([&](Lit l) { return !assumptions.has(-l) && !reformObj->hasLit(l); });
  if (core->isTautology()) return State::FAIL;
  core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  if (!core->hasNegativeSlack(solver.getAssumptions().getIndex())) return State::FAIL;
  core->saturate(true, false);
  Ce32 cardCore = reduceToCardinality(core);
  assert(cardCore->hasNoZeroes());

  // adjust the lower bound
  assert(cardCore->nVars() > 0);
  SMALL mult = 0;
  for (Var v : cardCore->getVars()) {
    if (mult == 1) break;
    if (!reformObj->hasLit(cardCore->getLit(v))) continue;  // in case of user assumption
    mult = (mult == 0) ? aux::abs(reformObj->coefs[v]) : std::min(mult, aux::abs(reformObj->coefs[v]));
  }
  if (mult == 0) return State::FAIL;  // no further literals of the objective remain

  global.stats.NCGNONCLAUSALCORES += !cardCore->isClause();

  int cardUpperBound = static_cast<int>(upper_bound / mult);
  bool needAuxiliary = cardUpperBound > cardCore->getDegree();
  if (needAuxiliary) {
    // add auxiliary variable
    int newN = solver.getNbVars() + 1;
    solver.setNbVars(newN, false);
    reformObj->addLhs(mult, newN);  // add only one variable for now

    // add first lazy constraint
    lazyVars.push_back(std::make_unique<LazyVar<SMALL, LARGE>>(solver, cardCore, newN, mult, cardUpperBound));
    lazyVars.back()->addAtLeastConstraint();
    lazyVars.back()->addAtMostConstraint();
  }
  // else the cardinality is actually an equality, and no auxiliary variables are needed.

  // reformulate the objective
  cardCore->invert();
  reformObj->addUp(cardCore, mult);
  simplifyAssumps(reformObj, assumptions);

  if (!needAuxiliary) {
    // since the cardinality is actually an equality, we can add its inverted form to the solver
    solver.addConstraint(cardCore, Origin::COREGUIDED);
  }

  lower_bound = -reformObj->getDegree();
  addLowerBound();
  return State::SUCCESS;
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::handleInconsistency(const CeSuper& core) {
  // modifies core
  // returns true iff the inconsistency is due to user assumptions
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  lower_bound = -reformObj->getDegree();

  if (core) {
    core->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    core->saturate(true, false);
  }
  if (!core || core->isTautology()) {
    // only violated unit assumptions were derived
    assert(solver.assumptionsClashWithUnits());
    ++global.stats.NCGUNITCORES;
    addLowerBound();
    checkLazyVariables();
    return std::any_of(assumptions.getKeys().begin(), assumptions.getKeys().end(),
                       [&](Lit l) { return isUnit(solver.getLevel(), -l); });
  }
  assert(!core->hasNegativeSlack(solver.getLevel()));  // root inconsistency was handled by solver's learnConstraint
  if (core->falsifiedBy(assumptions)) return true;
  assert(core->hasNegativeSlack(solver.getAssumptions().getIndex()));

  --global.stats.NCGCOREREUSES;
  State result = State::SUCCESS;
  while (result == State::SUCCESS) {
    ++global.stats.NCGCOREREUSES;
    result = reformObjective(core);
  }
  simplifyAssumps(reformObj, assumptions);

  checkLazyVariables();
  printObjBounds();
  return false;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::boundObjectiveBySolution(const std::vector<Lit>& sol) {
  assert(solver.checkSAT(sol));
  upper_bound = -origObj->getRhs();
  for (Var v : origObj->getVars()) upper_bound += sol[v] > 0 ? origObj->coefs[v] : 0;
  printObjBounds();

  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  std::pair<ID, ID> res = solver.addConstraint(aux, Origin::UPPERBOUND);
  lastUpperBound = res.second;
  if (assumptions.isEmpty()) harden();
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::harden() {
  // NOTE: this does not play nice with assumptions which impact the upper and lower bounds
  assert(assumptions.isEmpty());
  LARGE diff = upper_bound - lower_bound;
  for (Var v : reformObj->getVars()) {
    if (aux::abs(reformObj->coefs[v]) > diff) {
      solver.addUnitConstraint(-reformObj->getLit(v), Origin::HARDENEDBOUND);
    }
  }
}

void decreaseStratLim(bigint& stratLim, const bigint& stratDiv) {
  bigint smaller = (stratFactor * stratLim) / stratDiv;
  if (smaller < 1) {
    stratLim = 1;
  } else if (smaller >= stratLim) {
    --stratLim;
  } else {
    stratLim = smaller;
  }
  assert(stratLim >= 1);
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::run(bool optimize) {
  try {
    solver.presolve();  // will run only once, but also short-circuits (throws UnsatEncounter) when unsat was reached
  } catch (const UnsatEncounter& ue) {
    return SolveState::UNSAT;
  }
  coreguided = coreguided && optimize;
  while (true) {
    // NOTE: it's possible that upper_bound < lower_bound, since at the point of optimality, the objective-improving
    // constraint yields UNSAT, at which case core-guided search can derive any constraint.
    StatNum current_time = global.stats.getDetTime();
    if (reply == SolveState::INPROCESSED && global.options.printCsvData) {
      global.stats.printCsvLine(static_cast<StatNum>(lower_bound), static_cast<StatNum>(upper_bound));
    }

    // There are three possibilities:
    // - no assumptions are set (because something happened during previous core-guided step)
    // - only the given assumptions are set (because the previous step was not core-guided)
    // - more than only the given assumptions are set (because the previous core-guided step did not finish)
    // NOTE: what if no coreguided possible because all variables of the objective are assumed?

    assert(!coreguided || optimize);
    if (coreguided &&
        solver.getAssumptions().size() <= assumptions.size()) {  // figure out and set new coreguided assumptions
      reformObj->removeEqualities(solver.getEqualities(), false);
      simplifyAssumps(reformObj, assumptions);
      reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
      if (reformObj->nVars() == 0) {
        solver.setAssumptions(assumptions.getKeys());
      } else {
        std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than bigint
        litcoefs.reserve(reformObj->nVars());
        while (true) {
          for (Var v : reformObj->getVars()) {
            assert(reformObj->getLit(v) != 0);
            assert(!assumptions.has(v));
            assert(!assumptions.has(-v));
            if (stratLim <= reformObj->coefs[v] || stratLim <= -reformObj->coefs[v]) {
              litcoefs.emplace_back(aux::toDouble(aux::abs(reformObj->coefs[v])), v);
            }
          }
          if (!litcoefs.empty() || stratLim == 1) break;
          decreaseStratLim(stratLim, stratDiv);
        }
        std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double>& t1, const Term<double>& t2) {
          return t1.c > t2.c || (t1.c == t2.c && t1.l < t2.l);
        });
        std::vector<Lit> assumps = assumptions.getKeys();
        assumps.reserve(assumps.size() + litcoefs.size());
        for (const Term<double>& t : litcoefs) assumps.push_back(-reformObj->getLit(t.l));
        solver.setAssumptions(assumps);
        assert(solver.getAssumptions().size() > assumptions.size());
      }
    } else if (!coreguided) {  // set regular assumptions
      solver.setAssumptions(assumptions.getKeys());
    }

    if (solver.lastGlobalDual && solver.lastGlobalDual->hasNegativeSlack(solver.getAssumptions().getIndex())) {
      // NOTE: this optimization really helps with knapsack instances, because it immediately fixes a bunch of variables
      // TODO: generalize this: reformulate the *original* objective with the new bound after an inconsistency?
      reply = SolveState::INCONSISTENT;
      solver.lastCore = solver.lastGlobalDual;
    } else {
      try {
        reply = aux::timeCall<SolveState>([&] { return solver.solve(); }, solver.hasAssumptions()
                                                                              ? global.stats.SOLVETIMEASSUMP
                                                                              : global.stats.SOLVETIMEFREE);
      } catch (const UnsatEncounter& ue) {
        reply = SolveState::UNSAT;
      }
      if (solver.hasAssumptions()) {
        global.stats.DETTIMEASSUMP += global.stats.getDetTime() - current_time;
      } else {
        global.stats.DETTIMEFREE += global.stats.getDetTime() - current_time;
      }
    }

    if (reply == SolveState::UNSAT) {
      return SolveState::UNSAT;
    } else if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++global.stats.NSOLS;
      ++solutionsFound;
      if (optimize) {
        boundObjectiveBySolution(solver.getLastSolution());
      }
      if (coreguided) {
        decreaseStratLim(stratLim, stratDiv);
        solver.clearAssumptions();
      }
      return SolveState::SAT;
    } else if (reply == SolveState::INCONSISTENT) {
      assert(!solver.getAssumptions().isEmpty());
      ++global.stats.NCORES;
      if (solver.getAssumptions().size() > assumptions.size()) {
        assert(coreguided);
        if (handleInconsistency(solver.lastCore)) {
          solver.clearAssumptions();
          return SolveState::INCONSISTENT;
        } else {
          solver.clearAssumptions();
        }
      } else {
        assert(solver.getAssumptions().size() == assumptions.size());  // no coreguided assumptions
        return SolveState::INCONSISTENT;
      }
    } else if (reply == SolveState::INPROCESSED) {
      bool oldcoreguided = coreguided;
      coreguided = optimize && lower_bound < upper_bound &&
                   (global.options.cgHybrid.get() >= 1 ||
                    global.stats.DETTIMEASSUMP <
                        global.options.cgHybrid.get() * (global.stats.DETTIMEFREE + global.stats.DETTIMEASSUMP));
      // NOTE: no need to do coreguided search once we know the lower bound is at least the upper bound
      // in that case, let the solver figure out the inconsistency on its own
      if (oldcoreguided && !coreguided && stratLim > 1) {
        // next time, use more assumption lits
        decreaseStratLim(stratLim, stratDiv);
      }
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

template struct LazyVar<int, long long>;
template struct LazyVar<long long, int128>;
template struct LazyVar<int128, int128>;
template struct LazyVar<int128, int256>;
template struct LazyVar<bigint, bigint>;

}  // namespace xct
