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

#include "Solver.hpp"
#include "auxiliary.hpp"
#include "constraints/Constr.hpp"
#include "globals.hpp"

namespace xct {

// ---------------------------------------------------------------------
// Initialization

Solver::Solver(ILP& i)
    : ilp(i),
      n(0),
      assumptions_lim({0}),
      equalities(*this),
      implications(*this),
      nconfl_to_reduce(0),
      nconfl_to_restart(0) {
  ca.capacity(1024 * 1024);  // 4MB
  position.resize(1, INF);
}

Solver::~Solver() {
  for (CRef cr : constraints) {
    ca[cr].freeUp();
  }
}

void Solver::setNbVars(int nvars, bool orig) {
  assert(nvars > 0);
  assert(nvars < INF);
  if (nvars <= n) {
    assert(isOrig(nvars) == orig);
    return;
  }
  adj.resize(nvars, {});
  level.resize(nvars, INF);
  position.resize(nvars + 1, INF);
  reason.resize(nvars + 1, CRef_Undef);
  freeHeur.resize(nvars + 1);
  cgHeur.resize(nvars + 1);
  cePools.resize(nvars + 1);
  // if (lpSolver) lpSolver->setNbVariables(nvars + 1); // Currently, LP solver only reasons on formula constraints
  equalities.setNbVars(nvars);
  implications.setNbVars(nvars);
  isorig.resize(nvars + 1, orig);
  ranks.resize(nvars + 1, 0);
  tabuSol.resize(nvars + 1, 0);
  lit2cons.resize(nvars, {});
  lit2consOldSize.resize(nvars, std::numeric_limits<int>::max());
  if (orig) {
    for (Var v = n + 1; v <= nvars; ++v) {
      tabuSol[v] = -v;
    }
    stats.NORIGVARS.z += nvars - n;
  } else {
    stats.NAUXVARS.z += nvars - n;
  }
  n = nvars;
}

void Solver::init(const CeArb& obj) {
  for (Var v : obj->vars) {
    objectiveLits.add(obj->getLit(v));
  }
  nconfl_to_restart = options.lubyMult.get();
  nconfl_to_reduce = 1000;
  if (options.randomSeed.get() != 1) {
    aux::timeCallVoid([&] { heur->randomize(getPos()); }, stats.HEURTIME);
  }
}

// ---------------------------------------------------------------------
// Assignment manipulation

void Solver::enqueueUnit(Lit l, Var v, CRef r) {
  assert(toVar(l) == v);
  assert(stats.NUNITS == trail.size());
  ++stats.NUNITS;
  reason[v] = CRef_Undef;  // no need to keep track of reasons for unit literals
  if (logger) {
    CeSuper tmp = ca[r].toExpanded(cePools);
    tmp->simplifyToUnit(level, position, v);
    logger->logUnit(tmp);
    assert(logger->getNbUnitIDs() == (int)trail.size() + 1);
  }
  if (options.tabuLim.get() != 0 && isOrig(v) && tabuSol[v] != l) {
    cutoff = ranks[v];
    flipTabu(l);
  }
}

void Solver::uncheckedEnqueue(Lit l, CRef r) {
  assert(!isTrue(level, l));
  assert(!isFalse(level, l));
  assert(isUnknown(position, l));
  Var v = toVar(l);
  reason[v] = r;
  if (decisionLevel() == 0) {
    enqueueUnit(l, v, r);
  }
  level[l] = decisionLevel();
  position[v] = (int)trail.size();
  trail.push_back(l);
}

void Solver::undoOne() {
  assert(!trail.empty());
  ++stats.NTRAILPOPS;
  Lit l = trail.back();
  if (qhead == (int)trail.size()) {
    for (const Watch& w : adj[-l])
      if (w.idx >= INF) ca[w.cref].undoFalsified(w.idx);
    --qhead;
  }
  Var v = toVar(l);
  trail.pop_back();
  level[l] = INF;
  position[v] = INF;
  heur->undoOne(v, l);
  if (isDecided(reason, v)) {
    assert(!trail_lim.empty());
    assert(trail_lim.back() == (int)trail.size());
    trail_lim.pop_back();
    if (decisionLevel() < assumptionLevel()) {
      assumptions_lim.pop_back();
    }
  }
  equalities.notifyBackjump();
  implications.notifyBackjump();
}

void Solver::backjumpTo(int lvl) {
  assert(lvl >= 0);
  while (decisionLevel() > lvl) undoOne();
}

void Solver::decide(Lit l) {
  ++stats.NDECIDE;
  trail_lim.push_back(trail.size());
  uncheckedEnqueue(l, CRef_Undef);
}

void Solver::propagate(Lit l, CRef r) {
  assert(isValid(r));
  ++stats.NPROP;
  uncheckedEnqueue(l, r);
}

State Solver::probe(Lit l, bool deriveImplications) {
  assert(decisionLevel() == 0);
  assert(isUnknown(getPos(), l));
  ++stats.NPROBINGS;
  decide(l);
  std::pair<CeSuper, State> result =
      aux::timeCall<std::pair<CeSuper, State>>([&] { return runPropagation(); }, stats.PROPTIME);
  if (result.second == State::UNSAT) {
    return State::UNSAT;
  } else if (result.second == State::FAIL) {
    CeSuper analyzed = aux::timeCall<CeSuper>([&] { return analyze(result.first); }, stats.CATIME);
    ID res = aux::timeCall<ID>([&] { return learnConstraint(analyzed, Origin::LEARNED); }, stats.LEARNTIME);
    return res == ID_Unsat ? State::UNSAT : State::FAIL;
  } else if (decisionLevel() == 0) {  // some missing propagation at level 0 could be made
    return State::FAIL;
  }
  assert(decisionLevel() == 1);
  if (deriveImplications) {
    implications.removeImplied(l);
    for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
      implications.addImplied(-trail[i], -l);  // the system may not be able to derive these
    }
    stats.NPROBINGIMPLMEM.z = std::max<StatNum>(stats.NPROBINGIMPLMEM.z, implications.nImpliedsInMemory());
  }
  return State::SUCCESS;
}

/**
 * Unit propagation with watched literals.
 * @post: all watches up to trail[qhead] have been propagated
 */
std::pair<CeSuper, State> Solver::runDatabasePropagation() {
  while (qhead < (int)trail.size()) {
    Lit p = trail[qhead++];
    std::vector<Watch>& ws = adj[-p];
    float prevStrength = std::numeric_limits<float>::max();
    int prevLBD = 0;
    for (int it_ws = 0; it_ws < (int)ws.size(); ++it_ws) {
      int idx = ws[it_ws].idx;
      if (idx < 0 && isTrue(level, idx + INF)) {
        assert(dynamic_cast<Clause*>(&(ca[ws[it_ws].cref])) != nullptr);
        continue;
      }  // blocked literal check
      CRef cr = ws[it_ws].cref;
      WatchStatus wstat = checkForPropagation(cr, ws[it_ws].idx, -p);
      if (wstat == WatchStatus::DROPWATCH) {
        aux::swapErase(ws, it_ws--);
      } else if (wstat == WatchStatus::CONFLICTING) {  // clean up current level and stop propagation
        ++stats.NTRAILPOPS;
        for (int i = 0; i <= it_ws; ++i) {
          const Watch& w = ws[i];
          if (w.idx >= INF) ca[w.cref].undoFalsified(w.idx);
        }
        --qhead;
        Constr& c = ca[cr];
        CeSuper result = c.toExpanded(cePools);
        c.decreaseLBD(result->getLBD(level));
        c.fixEncountered();
        return {result, State::FAIL};
      } else {
        assert(wstat == WatchStatus::KEEPWATCH);
        Constr& c = ca[cr];
        float cStrength = c.strength;
        int cLBD = c.lbd();
        if (cStrength > prevStrength || (cStrength == prevStrength && cLBD < prevLBD)) {
          assert(it_ws > 0);
          std::swap(ws[it_ws], ws[it_ws - 1]);
        }
        prevStrength = cStrength;
        prevLBD = cLBD;
      }
    }
  }
  return {CeNull(), State::SUCCESS};
}

std::pair<CeSuper, State> Solver::runPropagation() {
  while (true) {
    std::pair<CeSuper, State> result = runDatabasePropagation();
    if (result.second != State::SUCCESS) return result;
    State res = equalities.propagate();
    if (res == State::UNSAT) return {CeNull(), State::UNSAT};
    if (res == State::FAIL) continue;
    res = implications.propagate();
    if (res == State::UNSAT) return {CeNull(), State::UNSAT};
    if (res == State::SUCCESS) return {CeNull(), State::SUCCESS};
  }
}

std::pair<CeSuper, State> Solver::runPropagationWithLP() {
  if (std::pair<CeSuper, State> result = runPropagation(); result.second != State::SUCCESS) return result;
  if (lpSolver) {
    auto [state, constraint] = aux::timeCall<std::pair<LpStatus, CeSuper>>(
        [&] { return lpSolver->checkFeasibility(false); }, stats.LPTOTALTIME);
    if (state == LpStatus::UNSAT) return {CeNull(), State::UNSAT};
    // NOTE: calling LP solver may increase the propagations on the trail due to added constraints
    if (state == LpStatus::INFEASIBLE || state == LpStatus::OPTIMAL) {
      // added a Farkas/bound constraint and potentially backjumped, so we propagate again
      return runPropagation();
    }
  }
  return {CeNull(), State::SUCCESS};
}

WatchStatus Solver::checkForPropagation(CRef cr, int& idx, Lit p) {
  assert(isFalse(level, p));
  Constr& c = ca[cr];
  if (c.isMarkedForDelete()) return WatchStatus::DROPWATCH;
  ++stats.NWATCHLOOKUPS;

  return c.checkForPropagation(cr, idx, p, *this);
}

// ---------------------------------------------------------------------
// Conflict analysis

CeSuper getAnalysisCE(const CeSuper& conflict, int bitsOverflow, ConstrExpPools& cePools) {
  if (bitsOverflow == 0 || bitsOverflow > limitBitConfl<int128, int256>()) {
    CeArb confl = cePools.takeArb();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > limitBitConfl<int128, int128>()) {
    Ce128 confl = cePools.take128();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > limitBitConfl<long long, int128>()) {
    Ce96 confl = cePools.take96();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > limitBitConfl<int, long long>()) {
    Ce64 confl = cePools.take64();
    conflict->copyTo(confl);
    return confl;
  } else {
    Ce32 confl = cePools.take32();
    conflict->copyTo(confl);
    return confl;
  }
}

CeSuper Solver::analyze(const CeSuper& conflict) {
  if (logger) logger->logComment("Analyze");
  assert(conflict->hasNegativeSlack(level));
  conflict->removeUnitsAndZeroes(level, position);
  conflict->saturateAndFixOverflow(getLevel(), options.bitsOverflow.get(), options.bitsReduced.get(), 0);

  CeSuper confl = getAnalysisCE(conflict, options.bitsOverflow.get(), cePools);
  conflict->reset(false);

  IntSet& actSet = isPool.take();  // will hold the literals that need their activity bumped
  for (Var v : confl->getVars()) {
    if (isFalse(level, confl->getLit(v))) {
      actSet.add(v);
    }
  }

resolve:
  while (decisionLevel() > 0) {
    quit::checkInterrupt();
    Lit l = trail.back();
    if (confl->hasLit(-l)) {
      assert(confl->hasNegativeSlack(level));
      AssertionStatus status = confl->isAssertingBefore(level, decisionLevel());
      if (status == AssertionStatus::ASSERTING)
        break;
      else if (status == AssertionStatus::FALSIFIED) {
        backjumpTo(decisionLevel() - 1);
        assert(confl->hasNegativeSlack(level));
        continue;
      }
      assert(isPropagated(reason, l));
      Constr& reasonC = ca[reason[toVar(l)]];

      int lbd = reasonC.resolveWith(confl, l, *this, actSet);
      reasonC.decreaseLBD(lbd);
      reasonC.fixEncountered();
    }
    undoOne();
  }
  if (options.learnedMin && decisionLevel() > 0) {
    minimize(confl);
    if (confl->isAssertingBefore(level, decisionLevel()) != AssertionStatus::ASSERTING) goto resolve;
  }

  aux::timeCallVoid([&] { heur->vBumpActivity(actSet.getKeysMutable(), getPos()); }, stats.HEURTIME);
  isPool.release(actSet);

  assert(confl->hasNegativeSlack(level));
  return confl;
}

void Solver::minimize(const CeSuper& conflict) {
  assert(conflict->isSaturated());
  assert(conflict->isAssertingBefore(getLevel(), decisionLevel()) == AssertionStatus::ASSERTING);
  IntSet& saturatedLits = isPool.take();
  conflict->removeZeroes();
  conflict->getSaturatedLits(saturatedLits);
  if (saturatedLits.isEmpty()) {
    isPool.release(saturatedLits);
    return;
  }

  std::vector<std::pair<int, Lit>> litsToSubsume;
  litsToSubsume.reserve(conflict->nVars());
  for (Var v : conflict->getVars()) {
    Lit l = conflict->getLit(v);
    if (isFalse(getLevel(), l) && isPropagated(reason, l)) {
      litsToSubsume.push_back({position[v], l});
    }
  }
  std::sort(litsToSubsume.begin(), litsToSubsume.end(),
            [&](const std::pair<int, Lit>& x, const std::pair<int, Lit>& y) { return x.first > y.first; });

  for (const std::pair<int, Lit>& pr : litsToSubsume) {
    Lit l = pr.second;
    assert(conflict->getLit(toVar(l)) != 0);
    Constr& reasonC = ca[reason[toVar(l)]];
    int lbd =
        aux::timeCall<bool>([&] { return reasonC.subsumeWith(conflict, -l, *this, saturatedLits); }, stats.MINTIME);
    if (lbd > 0) {
      reasonC.decreaseLBD(lbd);
      reasonC.fixEncountered();
    }
    if (saturatedLits.isEmpty()) break;
  }
  conflict->removeZeroes();  // remove weakened literals
  isPool.release(saturatedLits);
}

State Solver::extractCore(const CeSuper& conflict, Lit l_assump) {
  if (l_assump != 0) {  // l_assump is an assumption propagated to the opposite value
    assert(assumptions.has(l_assump));
    assert(isFalse(level, l_assump));
    int pos = position[toVar(l_assump)];
    while ((int)trail.size() > pos) undoOne();
    assert(isUnknown(position, l_assump));
    decide(l_assump);
  }

  // Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
  // For this, we first copy the trail, then backjump to 0, then rebuild the trail.
  // Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
  std::vector<Lit> decisions;  // holds the decisions
  decisions.reserve(decisionLevel());
  std::vector<Lit> props;  // holds the propagations
  props.reserve(trail.size());
  assert(!trail_lim.empty());
  for (int i = trail_lim[0]; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (assumptions.has(l) && !(isPropagated(reason, l) && options.cgResolveProp)) {
      decisions.push_back(l);
    } else {
      props.push_back(l);
    }
  }
  backjumpTo(0);

  for (Lit l : decisions) decide(l);
  for (Lit l : props) propagate(l, reason[toVar(l)]);

  assert(conflict->hasNegativeSlack(level));
  conflict->removeUnitsAndZeroes(level, position);
  conflict->saturateAndFixOverflow(getLevel(), options.bitsOverflow.get(), options.bitsReduced.get(), 0);
  assert(conflict->hasNegativeSlack(level));
  lastCore = getAnalysisCE(conflict, options.bitsOverflow.get(), cePools);
  conflict->reset(false);

  // analyze conflict to the point where we have a decision core
  IntSet& actSet = isPool.take();
  while (decisionLevel() > 0 && isPropagated(reason, trail.back())) {
    quit::checkInterrupt();
    Lit l = trail.back();
    if (lastCore->hasLit(-l)) {
      assert(isPropagated(reason, l));
      Constr& reasonC = ca[reason[toVar(l)]];

      int lbd = reasonC.resolveWith(lastCore, l, *this, actSet);
      reasonC.decreaseLBD(lbd);
      reasonC.fixEncountered();
    }
    undoOne();
  }

  aux::timeCallVoid([&] { heur->vBumpActivity(actSet.getKeysMutable(), getPos()); }, stats.HEURTIME);
  isPool.release(actSet);

  // weaken non-falsifieds
  assert(lastCore->hasNegativeSlack(assumptions));
  assert(!lastCore->isTautology());
  assert(lastCore->isSaturated());
  for (Var v : lastCore->getVars()) {
    if (!assumptions.has(-lastCore->getLit(v))) {
      lastCore->weaken(v);
    }
  }
  assert(lastCore->hasNegativeSlack(assumptions));
  ID res = aux::timeCall<ID>([&] { return learnConstraint(lastCore, Origin::LEARNED); },
                             stats.LEARNTIME);  // NOTE: takes care of inconsistency
  if (res == ID_Unsat) return State::UNSAT;
  backjumpTo(0);
  lastCore->postProcess(getLevel(), getPos(), getHeuristic(), true);
  if (!lastCore->hasNegativeSlack(assumptions)) {  // apparently unit clauses were propagated during learnConstraint
    lastCore.makeNull();
  }
  return State::SUCCESS;
}

// ---------------------------------------------------------------------
// Constraint management

CRef Solver::attachConstraint(const CeSuper& constraint, bool locked) {
  assert(constraint->isSortedInDecreasingCoefOrder());
  assert(constraint->isSaturated());
  assert(constraint->hasNoZeroes());
  assert(constraint->hasNoUnits(getLevel()));
  assert(!constraint->isTautology());
  assert(constraint->nVars() > 0);
  assert(!constraint->hasNegativeSlack(getLevel()));
  assert(constraint->orig != Origin::UNKNOWN);

  CRef cr = constraint->toConstr(ca, locked,
                                 logger ? logger->logProofLineWithInfo(constraint, "Attach") : ++Logger::last_proofID);
  Constr& c = ca[cr];
  c.initializeWatches(cr, *this);
  constraints.push_back(cr);
  if (usedInTabu(c.getOrigin())) {
    for (unsigned int i = 0; i < c.size; ++i) {
      Lit l = c.lit(i);
      assert(isOrig(toVar(l)));
      lit2cons[l].insert({cr, i});
    }
    c.initializeTabu(tabuSol);
    if (!c.isSatisfiedByTabu(tabuSol)) {
      addToTabu(cr);
    }
  }
  if (c.isAtMostOne() && c.size > 2) {
    uint64_t hash = c.size;
    for (unsigned int i = 0; i < c.size; ++i) {
      hash ^= aux::hash(c.lit(i));
    }
    if (auto bestsize = atMostOneHashes.find(hash); bestsize == atMostOneHashes.end() || bestsize->second < c.size) {
      atMostOneHashes[hash] = c.size;
    }
  }

  Origin orig = c.getOrigin();
  bool learned = isLearned(orig);
  if (learned) {
    stats.LEARNEDLENGTHSUM += c.size;
    stats.LEARNEDDEGREESUM += c.degree();
    stats.LEARNEDSTRENGTHSUM += c.strength;
  } else {
    stats.EXTERNLENGTHSUM += c.size;
    stats.EXTERNDEGREESUM += c.degree();
    stats.EXTERNSTRENGTHSUM += c.strength;
  }
  if (c.degree() == 1) {
    stats.NCLAUSESLEARNED += learned;
    stats.NCLAUSESEXTERN += !learned;
  } else if (c.largestCoef() == 1) {
    stats.NCARDINALITIESLEARNED += learned;
    stats.NCARDINALITIESEXTERN += !learned;
  } else {
    stats.NGENERALSLEARNED += learned;
    stats.NGENERALSEXTERN += !learned;
  }

  stats.NCONSFORMULA += orig == Origin::FORMULA;
  stats.NCONSDOMBREAKER += orig == Origin::DOMBREAKER;
  stats.NCONSLEARNED += orig == Origin::LEARNED;
  stats.NCONSBOUND += isBound(orig);
  stats.NCONSCOREGUIDED += orig == Origin::COREGUIDED;
  stats.NLPGOMORYCUTS += orig == Origin::GOMORY;
  stats.NLPDUAL += orig == Origin::DUAL;
  stats.NLPFARKAS += orig == Origin::FARKAS;
  stats.NPURELITS += orig == Origin::PURE;
  stats.NHARDENINGS += orig == Origin::HARDENEDBOUND;
  stats.NCONSREDUCED += orig == Origin::REDUCED;

  if (decisionLevel() == 0) {
    std::pair<CeSuper, State> result =
        aux::timeCall<std::pair<CeSuper, State>>([&] { return runPropagation(); }, stats.PROPTIME);
    if (result.second == State::UNSAT) {
      return CRef_Unsat;
    } else if (result.second == State::FAIL) {
      CeSuper& confl = result.first;
      assert(confl);
      assert(confl->hasNegativeSlack(getLevel()));
      if (logger) {
        confl->removeUnitsAndZeroes(level, position);
        logger->logInconsistency(confl);
      }
      return CRef_Unsat;
    }
  }

  return cr;
}

/**
 * Adds c as a learned constraint with origin orig.
 * Backjumps to the level where c is no longer conflicting, as otherwise we might miss propagations.
 * If conflicting at level 0, calls quit::exit_SUCCESS.
 */
ID Solver::learnConstraint(const CeSuper& ce, Origin orig) {
  assert(ce);
  assert(isLearned(orig));
  CeSuper learned = ce->clone(cePools);
  learned->orig = orig;
  if (orig != Origin::EQUALITY) learned->removeEqualities(getEqualities(), true);
  learned->selfSubsumeImplications(implications);
  learned->removeUnitsAndZeroes(getLevel(), getPos());
  if (learned->isTautology()) return ID_Undef;
  learned->saturateAndFixOverflow(getLevel(), options.bitsLearned.get(), options.bitsLearned.get(), 0);
  learned->sortInDecreasingCoefOrder(getHeuristic());
  auto [assertionLevel, isAsserting] = learned->getAssertionStatus(level, position);
  if (assertionLevel < 0) {
    backjumpTo(0);
    assert(learned->isInconsistency());
    if (logger) logger->logInconsistency(learned);
    return ID_Unsat;
  }
  backjumpTo(assertionLevel);
  assert(!learned->hasNegativeSlack(level));
  if (isAsserting) learned->heuristicWeakening(level, position);
  learned->postProcess(getLevel(), getPos(), getHeuristic(), false);
  assert(learned->isSaturated());
  if (learned->isTautology()) {
    return ID_Undef;
  }
  CRef cr = attachConstraint(learned, false);
  if (cr == CRef_Unsat) {
    return ID_Unsat;
  }
  Constr& c = ca[cr];
  c.decreaseLBD(isAsserting ? learned->getLBD(level) : learned->nVars());
  // the LBD of non-asserting constraints is undefined, so we take a safe upper bound
  stats.LEARNEDLBDSUM += c.lbd();
  return c.id;
}

ID Solver::learnUnitConstraint(Lit l, Origin orig, ID id) {
  assert(isLearned(orig));
  assert(!isUnit(getLevel(), l));
  assert(!isUnit(getLevel(), -l));
  // so no conflict after learning

  backjumpTo(0);
  Ce32 unit = cePools.take32();
  unit->orig = orig;
  unit->addRhs(1);
  unit->addLhs(1, l);
  if (id != ID_Undef) {
    unit->resetBuffer(id);
  }
  CRef cr = attachConstraint(unit, false);
  if (cr == CRef_Unsat) {
    return ID_Unsat;
  }
  Constr& c = ca[cr];
  c.decreaseLBD(1);

  return c.id;
}

ID Solver::learnClause(const std::vector<Lit>& lits, Origin orig, ID id) {
  ConstrSimple32 clause{{}, 1, orig, std::to_string(id) + " "};
  clause.terms.reserve(lits.size());
  for (Lit l : lits) {
    clause.terms.push_back({1, l});
  }
  return aux::timeCall<ID>([&] { return learnConstraint(clause.toExpanded(cePools), orig); }, stats.LEARNTIME);
}

std::pair<ID, ID> Solver::addInputConstraint(const CeSuper& ce) {
  assert(isInput(ce->orig));
  assert(decisionLevel() == 0);
  ID input = ID_Undef;
  if (logger) {
    switch (ce->orig) {
      case Origin::FORMULA:
        input = logger->logInput(ce);
        break;
        // TODO: reactivate below when VeriPB's redundant rule becomes stronger
        //      case Origin::PURE:
        //        input = logger->logPure(ce);
        //        break;
        //      case Origin::DOMBREAKER:
        //        input = logger->logDomBreaker(ce);
        //        break;
      default:
        input = logger->logAssumption(ce);
    }
  }
  ce->strongPostProcess(*this);
  if (ce->isTautology()) {
    return {input, ID_Undef};  // already satisfied.
  }

  if (ce->hasNegativeSlack(level)) {
    assert(decisionLevel() == 0);
    assert(ce->hasNoUnits(level));
    assert(ce->isInconsistency());
    if (options.verbosity.get() > 0) {
      std::cout << "c Conflicting input constraint" << std::endl;
    }
    if (logger) logger->logInconsistency(ce);
    return {input, ID_Unsat};
  }

  CRef cr = attachConstraint(ce, true);
  if (cr == CRef_Unsat) {
    return {input, ID_Unsat};
  }
  ID id = ca[cr].id;
  Origin orig = ca[cr].getOrigin();
  if (isExternal(orig)) {
    external[id] = cr;
  }
  if (lpSolver && (orig == Origin::FORMULA || isBound(orig))) {
    lpSolver->addConstraint(cr, false, orig == Origin::UPPERBOUND, orig == Origin::LOWERBOUND);
  }
  return {input, id};
}

std::pair<ID, ID> Solver::addConstraint(const CeSuper& c, Origin orig) {
  // NOTE: copy to temporary constraint guarantees original constraint is not changed and does not need logger
  CeSuper ce = c->clone(cePools);
  ce->orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  return result;
}

std::pair<ID, ID> Solver::addConstraint(const ConstrSimpleSuper& c, Origin orig) {
  CeSuper ce = c.toExpanded(cePools);
  ce->orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  return result;
}

ID Solver::addUnitConstraint(Lit l, Origin orig) { return addConstraint(ConstrSimple32({{1, l}}, 1), orig).second; }

std::pair<ID, ID> Solver::invalidateLastSol(const std::vector<Var>& vars) {
  assert(foundSolution());
  ConstrSimple32 invalidator;
  invalidator.terms.reserve(stats.NORIGVARS.z);
  invalidator.rhs = 1;
  for (Var v : vars) {
    invalidator.terms.push_back({1, -lastSol[v]});
  }
  return addConstraint(invalidator, Origin::INVALIDATOR);
}

void Solver::removeConstraint(const CRef& cr, [[maybe_unused]] bool override) {
  Constr& c = ca[cr];
  assert(override || !c.isLocked());
  assert(!c.isMarkedForDelete());
  assert(!external.count(c.id));
  c.header.markedfordel = 1;
  ca.wasted += c.getMemSize();
  if (usedInTabu(c.getOrigin())) {
    for (unsigned int i = 0; i < c.size; ++i) {
      Lit l = c.lit(i);
      assert(isOrig(toVar(l)));
      assert(lit2cons[l].count(cr));
      lit2cons[l].erase(cr);
    }
    eraseFromTabu(cr);
  }
}

void Solver::dropExternal(ID id, bool erasable, bool forceDelete) {
  assert(erasable || !forceDelete);
  if (id == ID_Undef) return;
  auto old_it = external.find(id);
  assert(old_it != external.end());
  CRef cr = old_it->second;
  external.erase(old_it);
  ca[cr].setLocked(!erasable);
  if (forceDelete) removeConstraint(cr);
}

CeSuper Solver::getIthConstraint(int i) const { return ca[constraints[i]].toExpanded(cePools); }

// ---------------------------------------------------------------------
// Assumptions

void Solver::setAssumptions(const std::vector<Lit>& assumps) {
  clearAssumptions();
  if (assumps.empty()) return;
  for (Lit l : assumps) {
    assumptions.add(l);
  }
  assumptions_lim.reserve((int)assumptions.size() + 1);
  if (options.varSeparate && !assumps.empty()) {
    heur = &cgHeur;
  }
}

void Solver::clearAssumptions() {
  assumptions.clear();
  backjumpTo(0);
  assert(assumptionLevel() == 0);
  assumptions_lim[0] = 0;
  heur = &freeHeur;
}

bool Solver::assumptionsClashWithUnits() const {
  return std::any_of(assumptions.getKeys().cbegin(), assumptions.getKeys().cend(),
                     [&](Lit l) { return isUnit(getLevel(), -l); });
}

int Solver::getNbUnits() const { return trail.size(); }

std::vector<Lit> Solver::getUnits() const {
  if (decisionLevel() == 0) return trail;
  std::vector<Lit> units;
  units.reserve(trail_lim[0]);
  for (int i = 0; i < trail_lim[0]; ++i) {
    Lit l = trail[i];
    if (!isOrig(toVar(l))) continue;
    units.push_back(l);
  }
  return units;
}

const std::vector<Lit>& Solver::getLastSolution() const { return lastSol; }

// ---------------------------------------------------------------------
// Garbage collection

void Solver::rebuildLit2Cons() {
  for (std::unordered_map<CRef, int>& col : lit2cons) {
    col.clear();
  }
  for (const CRef& cr : constraints) {
    Constr& c = ca[cr];
    if (c.isMarkedForDelete() || !usedInTabu(c.getOrigin())) continue;
    for (unsigned int i = 0; i < c.size; ++i) {
      assert(isOrig(toVar(c.lit(i))));
      lit2cons[c.lit(i)].insert({cr, c.isClauseOrCard() ? INF : i});
    }
  }
}

void updatePtr(const std::unordered_map<uint32_t, CRef>& crefmap, CRef& cr) { cr = crefmap.at(cr.ofs); }

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are deleted.
void Solver::garbage_collect() {
  assert(decisionLevel() == 0);  // otherwise reason CRefs need to be taken care of
  if (options.verbosity.get() > 1) std::cout << "c GARBAGE COLLECT" << std::endl;

  ca.wasted = 0;
  ca.at = 0;
  std::unordered_map<uint32_t, CRef> crefmap;
  for (int i = 1; i < (int)constraints.size(); ++i) assert(constraints[i - 1].ofs < constraints[i].ofs);
  for (CRef& cr : constraints) {
    uint32_t offset = cr.ofs;
    size_t memSize = ca[cr].getMemSize();
    memmove(ca.memory + ca.at, ca.memory + cr.ofs, sizeof(uint32_t) * memSize);
    cr.ofs = ca.at;
    ca.at += memSize;
    crefmap[offset] = cr;
  }

  for (Lit l = -n; l <= n; ++l) {
    for (Watch& w : adj[l]) updatePtr(crefmap, w.cref);
  }
  for (auto& ext : external) {
    updatePtr(crefmap, ext.second);
  }
  rebuildLit2Cons();
  rebuildTabu();
}

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are removed from memory.
State Solver::reduceDB() {
  backjumpTo(0);  // otherwise reason CRefs need to be taken care of
  std::vector<CRef> learnts;
  learnts.reserve(constraints.size());

  removeSatisfiedNonImpliedsAtRoot();
  for (const CRef& cr : constraints) {
    Constr& c = ca[cr];
    if (c.isMarkedForDelete() || c.isLocked() || external.count(c.id)) {
      continue;
    }
    assert(!usedInTabu(c.getOrigin()));
    if (c.isSatisfiedAtRoot(getLevel())) {
      ++stats.NSATISFIEDSREMOVED;
      removeConstraint(cr);
    } else if ((int)c.lbd() > options.dbSafeLBD.get()) {
      learnts.push_back(cr);  // Don't erase glue constraints
    }
  }

  std::sort(learnts.begin(), learnts.end(), [&](CRef x, CRef y) {
    int res = (int)ca[x].lbd() - (int)ca[y].lbd();
    return res < 0 || (res == 0 && ca[x].strength > ca[y].strength);
  });
  long long limit = std::pow(std::log(stats.NCONFL.z), options.dbExp.get());
  for (size_t i = limit; i < learnts.size(); ++i) {
    removeConstraint(learnts[i]);
  }

  int currentConstraints = constraints.size();
  for (int i = 0; i < currentConstraints; ++i) {
    CRef cr = constraints[i];
    Constr& c = ca[cr];
    if (c.isMarkedForDelete() || external.count(c.id) || !c.canBeSimplified(level, equalities)) continue;
    ++stats.NCONSREADDED;
    CeSuper ce = c.toExpanded(cePools);
    bool isLocked = c.isLocked();
    bool lbd = c.lbd();
    removeConstraint(cr, true);
    ce->strongPostProcess(*this);
    if (ce->isTautology()) continue;
    CRef crnew = attachConstraint(ce, isLocked);  // NOTE: this invalidates c!
    if (crnew == CRef_Unsat) return State::UNSAT;
    if (crnew == CRef_Undef) continue;
    ca[crnew].decreaseLBD(lbd);
  }

  for (Lit l = -n; l <= n; ++l) {
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (ca[adj[l][i].cref].isMarkedForDelete()) {
        aux::swapErase(adj[l], i--);
      }
    }
  }

  std::vector<int> cardPoints;
  long long reduced = 0;
  for (size_t i = limit; i < learnts.size(); ++i) {
    Constr& c = ca[learnts[i]];
    assert(c.isMarkedForDelete());
    if (!c.isClauseOrCard()) {
      ++reduced;
      CeSuper ce = c.toExpanded(cePools);
      ce->removeUnitsAndZeroes(getLevel(), getPos());
      if (ce->isTautology()) continue;  // possible due to further root propagations during rewriting of constraints
      ce->simplifyToCardinality(false, ce->getMaxStrengthCardinalityDegree(cardPoints));
      ID res = aux::timeCall<ID>([&] { return learnConstraint(ce, Origin::REDUCED); }, stats.LEARNTIME);
      if (res == ID_Unsat) return State::UNSAT;
    }
  }

  size_t j = 0;
  unsigned int decay = (unsigned int)options.dbDecayLBD.get();
  for (size_t i = 0; i < constraints.size(); ++i) {
    Constr& c = ca[constraints[i]];
    if (c.isMarkedForDelete()) {
      c.freeUp();  // free up indirectly owned memory before implicitly deleting c during garbage collect
    } else {
      c.decayLBD(decay);
      constraints[j++] = constraints[i];
    }
  }
  constraints.resize(j);
  if ((double)ca.wasted / (double)ca.at > 0.2) {
    aux::timeCallVoid([&] { garbage_collect(); }, stats.GCTIME);
  }
  return State::SUCCESS;
}

// ---------------------------------------------------------------------
// Solving

double Solver::luby(double y, int i) {
  // Find the finite subsequence that contains index 'i', and the
  // size of that subsequence:
  int size, seq;
  for (size = 1, seq = 0; size < i + 1; seq++, size = 2 * size + 1) {
  }
  while (size != i + 1) {
    size = (size - 1) >> 1;
    --seq;
    assert(size != 0);
    i = i % size;
  }
  return std::pow(y, seq);
}

bool Solver::checkSAT(const std::vector<Lit>& assignment) {
  return std::all_of(constraints.cbegin(), constraints.cend(), [&](CRef cr) {
    const Constr& c = ca[cr];
    return c.getOrigin() != Origin::FORMULA || c.toExpanded(cePools)->isSatisfied(assignment);
  });
}

std::pair<State, CeSuper> Solver::inProcess() {
  assert(decisionLevel() == 0);
  removeSatisfiedNonImpliedsAtRoot();
  if (options.pureLits) derivePureLits();
  if (options.domBreakLim.get() != 0) dominanceBreaking();
  if (options.inpAMO.get() != 0) {
    State state = aux::timeCall<State>([&] { return runAtMostOneDetection(); }, stats.ATMOSTONETIME);
    if (state == State::UNSAT) return {State::UNSAT, CeNull()};
  }
  // TODO: timing methods should be done via wrapper methods?

#if WITHSOPLEX
  if (lpSolver && lpSolver->canInProcess()) {
    return aux::timeCall<std::pair<State, CeSuper>>([&] { return lpSolver->inProcess(); }, stats.LPTOTALTIME);
  }
#endif  // WITHSOPLEX
  return {State::SUCCESS, CeNull()};
}

std::pair<State, CeSuper> Solver::presolve() {
  if (options.verbosity.get() > 0) std::cout << "c PRESOLVE" << std::endl;

  std::pair<State, CeSuper> res =
      aux::timeCall<std::pair<State, CeSuper>>([&] { return inProcess(); }, stats.INPROCESSTIME);

  if (res.first == State::UNSAT) return res;
#if WITHSOPLEX
  if (options.lpTimeRatio.get() > 0) {
    lpSolver = std::make_shared<LpSolver>(ilp);
    return aux::timeCall<std::pair<State, CeSuper>>([&] { return lpSolver->inProcess(); }, stats.LPTOTALTIME);
  }
#endif
  return {State::SUCCESS, CeNull()};
}

void Solver::removeSatisfiedNonImpliedsAtRoot() {
  assert(decisionLevel() == 0);
  std::vector<CRef> toCheck;
  for (int i = lastRemoveSatisfiedsTrail; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (!isOrig(toVar(l))) continue;  // no column view for auxiliary variables for now
    for (const std::pair<const CRef, int>& pr : lit2cons[l]) {
      Constr& c = ca[pr.first];
      assert(!c.isMarkedForDelete());  // should be erased from lit2cons when marked for delete
      if (c.isSeen()) continue;
      c.setSeen(true);
      toCheck.push_back(pr.first);
    }
  }
  for (const CRef& cr : toCheck) {
    Constr& c = ca[cr];
    assert(c.isSeen());
    c.setSeen(false);
    if (c.isSatisfiedAtRoot(getLevel()) && external.count(c.id) == 0) {  // upper bound constraints may yet be external
      ++stats.NSATISFIEDSREMOVED;
      removeConstraint(cr, true);
    }
  }
  lastRemoveSatisfiedsTrail = trail.size();
}

void Solver::derivePureLits() {
  assert(decisionLevel() == 0);
  for (Lit l = -getNbVars(); l <= getNbVars(); ++l) {
    quit::checkInterrupt();
    if (l == 0 || !isOrig(toVar(l)) || isKnown(getPos(), l) || objectiveLits.has(l) || equalities.isPartOfEquality(l) ||
        !lit2cons[-l].empty())
      continue;  // NOTE: core-guided variables will not be eliminated
    [[maybe_unused]] ID id = addUnitConstraint(l, Origin::PURE);
    assert(id != ID_Unsat);
    removeSatisfiedNonImpliedsAtRoot();
  }
}

void Solver::dominanceBreaking() {
  removeSatisfiedNonImpliedsAtRoot();
  std::unordered_set<Lit> inUnsaturatableConstraint;
  IntSet& saturating = isPool.take();
  IntSet& intersection = isPool.take();
  for (Lit l = -getNbVars(); l <= getNbVars(); ++l) {
    if (l == 0 || !isOrig(toVar(l)) || isKnown(getPos(), l) || objectiveLits.has(l) || equalities.isPartOfEquality(l))
      continue;
    assert(saturating.isEmpty());
    std::unordered_map<CRef, int>& col = lit2cons[-l];
    if (col.empty()) {
      [[maybe_unused]] ID id = addUnitConstraint(l, Origin::PURE);
      assert(id != ID_Unsat);
      removeSatisfiedNonImpliedsAtRoot();
      continue;
    }
    if ((options.domBreakLim.get() != -1 && (int)col.size() >= options.domBreakLim.get()) ||
        (int)col.size() >= lit2consOldSize[-l] || inUnsaturatableConstraint.count(-l)) {
      continue;
    }

    lit2consOldSize[-l] = col.size();
    Constr* first = &ca[col.cbegin()->first];
    unsigned int firstUnsatIdx = first->getUnsaturatedIdx();
    for (const std::pair<const CRef, int>& pr : col) {
      Constr& c = ca[pr.first];
      unsigned int unsatIdx = c.getUnsaturatedIdx();
      if (unsatIdx < firstUnsatIdx) {  // smaller number of starting lits
        first = &c;
        firstUnsatIdx = unsatIdx;
      }
      if (firstUnsatIdx == 0) {
        for (unsigned int i = 0; i < first->size; ++i) {
          inUnsaturatableConstraint.insert(first->lit(i));
        }
        break;
      }
    }
    assert(!first->isMarkedForDelete());
    for (unsigned int i = 0; i < firstUnsatIdx; ++i) {
      Lit ll = first->lit(i);
      assert(!isTrue(getLevel(), ll));  // otherwise the constraint would be satisfied and hence removed at the root
      if (!isFalse(getLevel(), ll)) {
        saturating.add(first->lit(i));
      }
    }
    saturating.remove(-l);  // if l is false, then we can not pick it to be true ;)
    auto range = binaryImplicants.equal_range(-l);
    for (auto it = range.first; it != range.second; ++it) {
      saturating.remove(-it->second);  // not interested in anything that already implies l TODO: is this needed?
    }
    for (const std::pair<const CRef, int>& pr : col) {
      if (saturating.isEmpty()) break;
      Constr& c = ca[pr.first];
      unsigned int unsatIdx = c.getUnsaturatedIdx();
      if (unsatIdx == 0) {
        for (unsigned int i = 0; i < c.size; ++i) {
          inUnsaturatableConstraint.insert(c.lit(i));
        }
      }
      assert(intersection.isEmpty());
      for (unsigned int i = 0; i < unsatIdx; ++i) {
        quit::checkInterrupt();
        Lit ll = c.lit(i);
        if (saturating.has(ll)) intersection.add(ll);
      }
      saturating = intersection;
      intersection.clear();
    }
    if (saturating.isEmpty()) continue;

    // saturating contains the intersection of the saturating literals for all constraints,
    // so asserting any literal in saturating makes l pure,
    // so we can add all these binary implicants as dominance breakers.
    for (Lit ll : saturating.getKeys()) {
      binaryImplicants.insert({ll, l});
      binaryImplicants.insert({-l, -ll});
      addConstraintUnchecked(ConstrSimple32{{{1, -ll}, {1, l}}, 1}, Origin::DOMBREAKER);
      removeSatisfiedNonImpliedsAtRoot();
    }
    saturating.clear();
  }
  isPool.release(saturating);
  isPool.release(intersection);
}

SolveState Solver::solve() {
  StatNum lastPropTime = stats.PROPTIME.z;
  StatNum lastCATime = stats.CATIME.z;
  StatNum lastNProp = stats.NPROP.z;
  bool runLP = false;
  while (true) {
    quit::checkInterrupt();
    CeSuper confl = CeNull();
    if (runLP) {
      auto [cnfl, state] =
          aux::timeCall<std::pair<CeSuper, State>>([&] { return runPropagationWithLP(); }, stats.PROPTIME);
      if (state == State::UNSAT) return SolveState::UNSAT;
      confl = cnfl;
    } else {
      std::pair<CeSuper, State> result =
          aux::timeCall<std::pair<CeSuper, State>>([&] { return runPropagation(); }, stats.PROPTIME);
      if (result.second == State::UNSAT) return SolveState::UNSAT;
      confl = result.first;
    }

    runLP = (bool)confl;
    if (confl) {
      assert(confl->hasNegativeSlack(level));
      ++stats.NCONFL;
      nconfl_to_restart--;
      long long nconfl = static_cast<long long>(stats.NCONFL.z);
      if (nconfl % 1000 == 0 && options.verbosity.get() > 0) {
        std::cout << "c " << nconfl << " confls " << constraints.size() << " constrs "
                  << getNbVars() - (long long)(stats.NUNITS.z + stats.NPROBINGEQS.z) << " vars" << std::endl;
        if (options.verbosity.get() > 2) {
          // memory usage
          std::cout << "c total constraint space: " << ca.cap * 4 / 1024. / 1024. << "MB" << std::endl;
          std::cout << "c total #watches: ";
          long long cnt = 0;
          for (Lit l = -n; l <= n; l++) cnt += (long long)adj[l].size();
          std::cout << cnt << std::endl;
        }
      }
      if (decisionLevel() == 0) {
        if (logger) {
          confl->removeUnitsAndZeroes(level, position);
          logger->logInconsistency(confl);
        }
        return SolveState::UNSAT;
      } else if (decisionLevel() > assumptionLevel()) {
        CeSuper analyzed = aux::timeCall<CeSuper>([&] { return analyze(confl); }, stats.CATIME);
        assert(analyzed);
        assert(analyzed->hasNegativeSlack(getLevel()));
        assert(analyzed->isSaturated());
        ID res = aux::timeCall<ID>([&] { return learnConstraint(analyzed, Origin::LEARNED); }, stats.LEARNTIME);
        if (res == ID_Unsat) return SolveState::UNSAT;
      } else {
        State state = aux::timeCall<State>([&] { return extractCore(confl); }, stats.CATIME);
        if (state == State::UNSAT) return SolveState::UNSAT;
        assert(!lastCore || lastCore->hasNegativeSlack(assumptions));
        return SolveState::INCONSISTENT;
      }
    } else {  // no conflict
      if (nconfl_to_restart <= 0) {
        backjumpTo(assumptionLevel());
        ++stats.NRESTARTS;
        double rest_base = luby(options.lubyBase.get(), static_cast<int>(stats.NRESTARTS.z));
        nconfl_to_restart = (long long)rest_base * options.lubyMult.get();
      }
      if (stats.NCONFL >= nconfl_to_reduce) {
        ++stats.NCLEANUP;
        nconfl_to_reduce += 1 + std::pow(std::log(stats.NCONFL.z), options.dbExp.get());

        if (options.verbosity.get() > 0) {
          StatNum propDiff = stats.PROPTIME.z - lastPropTime;
          StatNum cADiff = stats.CATIME.z - lastCATime;
          StatNum nPropDiff = stats.NPROP.z - lastNProp;
          std::cout << "c INPROCESSING " << propDiff << " proptime " << nPropDiff / propDiff << " prop/sec "
                    << propDiff / cADiff << " prop/ca" << std::endl;
          lastPropTime = stats.PROPTIME.z;
          lastCATime = stats.CATIME.z;
          lastNProp = stats.NPROP.z;
        }
        State state = aux::timeCall<State>([&] { return reduceDB(); }, stats.CLEANUPTIME);
        if (state == State::UNSAT) return SolveState::UNSAT;
        state = aux::timeCall<std::pair<State, CeSuper>>([&] { return inProcess(); }, stats.INPROCESSTIME).first;
        if (state == State::UNSAT) return SolveState::UNSAT;
        return SolveState::INPROCESSED;
      }
      Lit next = 0;
      assert(assumptionLevel() <= decisionLevel());
      if (assumptions_lim.back() < (int)assumptions.size()) {
        for (int i = (decisionLevel() == 0 ? 0 : trail_lim.back()); i < (int)trail.size(); ++i) {
          Lit l = trail[i];
          if (assumptions.has(-l)) {  // found conflicting assumption
            if (isUnit(level, l)) {   // negated assumption is unit
              backjumpTo(0);
              lastCore.makeNull();
              return SolveState::INCONSISTENT;
            } else {
              State state = aux::timeCall<State>(
                  [&] { return extractCore(ca[reason[toVar(l)]].toExpanded(cePools), -l); }, stats.CATIME);
              if (state == State::UNSAT) return SolveState::UNSAT;
              assert(!lastCore || lastCore->hasNegativeSlack(assumptions));
              return SolveState::INCONSISTENT;
            }
          }
        }
      }
      while (assumptions_lim.back() < (int)assumptions.size()) {
        assert(decisionLevel() == assumptionLevel());
        Lit l_assump = assumptions.getKeys()[assumptions_lim.back()];
        assert(!isFalse(level, l_assump));  // otherwise above check should have caught this
        if (isTrue(level, l_assump)) {      // assumption already propagated
          ++assumptions_lim.back();
        } else {  // unassigned assumption
          next = l_assump;
          assumptions_lim.push_back(assumptions_lim.back() + 1);
          break;
        }
      }
      if (next == 0) {
        next = aux::timeCall<Lit>([&] { return heur->pickBranchLit(getPos()); }, stats.HEURTIME);
      }
      if (next == 0) {
        assert((int)trail.size() == getNbVars());
        lastSol.resize(getNbVars() + 1);
        lastSol[0] = 0;
        for (Var v = 1; v <= getNbVars(); ++v) lastSol[v] = isOrig(v) ? (isTrue(level, v) ? v : -v) : 0;
        backjumpTo(0);
        return SolveState::SAT;
      }
      assert(next != 0);
      if (options.inpProbing && decisionLevel() == 0 && toVar(lastRestartNext) != toVar(next)) {
        State state = aux::timeCall<State>([&] { return probeRestart(next); }, stats.PROBETIME);
        if (state == State::UNSAT) return SolveState::UNSAT;
        assert(isKnown(getPos(), next));  // invariant of calling heur->pickBranchLit(...)
      } else {
        decide(next);
      }
      assert(isKnown(getPos(), next));
    }
  }
}

State Solver::probeRestart(Lit next) {
  lastRestartNext = toVar(next);
  int oldUnits = trail.size();
  State state = probe(-next, true);
  if (state == State::UNSAT) {
    return State::UNSAT;
  } else if (state == State::SUCCESS) {
    IntSet& trailSet = isPool.take();
    for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
      trailSet.add(trail[i]);
    }
    backjumpTo(0);
    std::vector<Lit> newUnits;
    State state = probe(next, true);
    if (state == State::UNSAT) {
      return State::UNSAT;
    } else if (state == State::SUCCESS) {
      for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
        Lit l = trail[i];
        if (trailSet.has(l)) {
          newUnits.push_back(l);
        } else if (trailSet.has(-l)) {
          equalities.merge(next, l);
        }
      }
      if (!newUnits.empty()) {
        backjumpTo(0);
        for (Lit l : newUnits) {
          assert(!isUnit(getLevel(), -l));
          if (!isUnit(getLevel(), l)) {
            ID res = aux::timeCall<ID>(
                [&] {
                  return learnUnitConstraint(l, Origin::PROBING, logger ? logger->logImpliedUnit(next, l) : ID_Undef);
                },
                stats.LEARNTIME);
            if (res == ID_Unsat) {
              return State::UNSAT;
            }
          }
        }
      }
    }
    isPool.release(trailSet);
  }
  stats.NPROBINGLITS += (decisionLevel() == 0 ? trail.size() : trail_lim[0]) - oldUnits;
  if (decisionLevel() == 0 && isUnknown(getPos(), next)) {
    decide(next);
  }
  assert(assumptionLevel() == 0);
  if (decisionLevel() == 1 && assumptions_lim.back() < (int)assumptions.size()) {
    assumptions_lim.push_back(assumptions_lim.back() + 1);
    // repair assumptions_lim
  }
  return State::SUCCESS;
}

State Solver::detectAtMostOne(Lit seed, std::unordered_set<Lit>& considered, std::vector<Lit>& previousProbe) {
  assert(decisionLevel() == 0);
  if (considered.count(seed)) {
    return State::FAIL;
  }
  if (isKnown(getPos(), seed)) {
    return State::SUCCESS;
  }
  State state = probe(-seed, true);
  if (state == State::UNSAT) {
    return State::UNSAT;
  } else if (state == State::FAIL) {
    return State::FAIL;  // found unit literals instead
  }

  // find candidates
  std::vector<Lit> candidates = {};
  assert(decisionLevel() == 1);
  candidates.reserve(trail.size() - trail_lim[0]);
  for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
    candidates.push_back(trail[i]);
  }
  backjumpTo(0);

  if (!previousProbe.empty()) {
    IntSet& previous = isPool.take();
    for (Lit l : previousProbe) {
      previous.add(l);
    }
    for (Lit l : candidates) {
      if (previous.has(l) && isUnknown(getPos(), l)) {
        assert(decisionLevel() == 0);
        ID res = aux::timeCall<ID>(
            [&] {
              return learnUnitConstraint(l, Origin::PROBING, logger ? logger->logImpliedUnit(seed, l) : ID_Undef);
            },
            stats.LEARNTIME);
        if (res == ID_Unsat) {
          return State::UNSAT;
        }
      } else if (previous.has(-l)) {
        equalities.merge(-seed, l);
      }
    }
    isPool.release(previous);
  } else {
    previousProbe = candidates;
  }

  // check whether at least three of them form a clique
  std::vector<Lit> cardLits = {seed};  // clique so far
  std::sort(candidates.begin(), candidates.end(),
            [&](Lit x, Lit y) { return getHeuristic().getActivity(toVar(x)) < getHeuristic().getActivity(toVar(y)); });
  assert(candidates.size() <= 1 ||
         getHeuristic().getActivity(toVar(candidates[0])) <= getHeuristic().getActivity(toVar(candidates[1])));
  while (candidates.size() > 1) {
    assert(decisionLevel() == 0);
    quit::checkInterrupt();
    Lit current = candidates.back();
    candidates.pop_back();
    if (isKnown(getPos(), current)) continue;
    State state = probe(-current, false);
    if (state == State::UNSAT) {
      return State::UNSAT;
    } else if (state == State::FAIL) {
      continue;
    }
    IntSet& trailSet = isPool.take();
    for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
      trailSet.add(trail[i]);
    }
    backjumpTo(0);
    for (Lit l : cardLits) {
      if (trailSet.has(-l) && isUnknown(getPos(), l)) {
        assert(decisionLevel() == 0);
        isPool.release(trailSet);
        ID res = aux::timeCall<ID>(
            [&] {
              return learnUnitConstraint(l, Origin::PROBING, logger ? logger->logImpliedUnit(l, current) : ID_Undef);
            },
            stats.LEARNTIME);
        if (res == ID_Unsat) {
          return State::UNSAT;
        }
        continue;
      }
    }
    if (std::any_of(candidates.begin(), candidates.end(), [&](Lit l) { return trailSet.has(l); })) {
      cardLits.push_back(current);  // found an additional cardinality lit
      candidates.erase(std::remove_if(candidates.begin(), candidates.end(), [&](Lit l) { return !trailSet.has(l); }),
                       candidates.end());
    }
    assert(!candidates.empty());
    isPool.release(trailSet);
  }
  for (Lit l : candidates) {
    cardLits.push_back(l);
  }
  for (Lit l : cardLits) {
    considered.insert(l);
  }
  for (int i = 0; i < (int)cardLits.size(); ++i) {
    if (isUnit(getLevel(), -cardLits[i])) {
      aux::swapErase(cardLits, i--);
    }
  }
  if (cardLits.size() > 2) {
    uint64_t hash = aux::hashForSet(cardLits);
    if (auto bestsize = atMostOneHashes.find(hash);
        bestsize != atMostOneHashes.end() && bestsize->second >= cardLits.size()) {
      return State::FAIL;
    }
    atMostOneHashes[hash] = cardLits.size();
    ConstrSimple32 card{{}, (int)cardLits.size() - 1};
    for (Lit l : cardLits) {
      card.terms.push_back({1, l});
    }
    ++stats.ATMOSTONES;
    CeSuper ce = card.toExpanded(cePools);
    if (logger) {
      ce->resetBuffer(logger->logAtMostOne(card));
    }
    ID res = aux::timeCall<ID>([&] { return learnConstraint(ce, Origin::DETECTEDAMO); }, stats.LEARNTIME);
    return res == ID_Unsat ? State::UNSAT : State::SUCCESS;
  } else {
    return State::FAIL;
  }
}

State Solver::runAtMostOneDetection() {
  assert(decisionLevel() == 0);
  int currentUnits = trail.size();
  DetTime currentDetTime = stats.getDetTime();
  DetTime oldDetTime = currentDetTime;
  std::vector<Lit> previous;
  std::unordered_set<Lit> considered;
  Lit next = heur->nextInActOrder(0);  // first in activity order
  while (next != 0 &&
         (options.inpAMO.get() == 1 ||
          stats.ATMOSTONEDETTIME < options.inpAMO.get() * std::max(options.basetime.get(), currentDetTime))) {
    previous.clear();
    if (detectAtMostOne(-next, considered, previous) == State::UNSAT) return State::UNSAT;
    if (detectAtMostOne(next, considered, previous) == State::UNSAT) return State::UNSAT;
    next = heur->nextInActOrder(next);
    oldDetTime = currentDetTime;
    currentDetTime = stats.getDetTime();
    stats.ATMOSTONEDETTIME += currentDetTime - oldDetTime;
  }
  stats.NATMOSTONEUNITS += trail.size() - currentUnits;
  return State::SUCCESS;
}

void Solver::addToTabu(const CRef& cr) {
  assert(usedInTabu(ca[cr].getOrigin()));
  assert(isValid(cr));
  assert(!violatedPtrs.count(cr));
  assert(!ca[cr].isSatisfiedByTabu(tabuSol));
  assert(!ca[cr].isMarkedForDelete());
  violatedQueue.push_front(cr);
  violatedPtrs.insert({cr, violatedQueue.cbegin()});
  assert(*violatedPtrs[cr] == cr);
}

void Solver::eraseFromTabu(const CRef& cr) {
  assert(usedInTabu(ca[cr].getOrigin()));
  std::unordered_map<CRef, std::list<CRef>::const_iterator>::iterator node = violatedPtrs.find(cr);
  if (node == violatedPtrs.end()) return;
  assert(*node->second == cr);
  violatedQueue.erase(node->second);
  violatedPtrs.erase(node);
  assert(!violatedPtrs.count(cr));
}

void Solver::rebuildTabu() {
  violatedQueue.clear();
  violatedPtrs.clear();
  for (const CRef& cr : constraints) {
    Constr& c = ca[cr];
    if (!usedInTabu(c.getOrigin()) || c.isMarkedForDelete() || c.isSatisfiedByTabu(tabuSol)) continue;
    addToTabu(cr);
  }
}

bool Solver::runTabuOnce() {
  assert(stats.NCLEANUP >= 0);
  std::vector<Lit> changeds;
  DetTime currentDetTime = stats.getDetTime();
  DetTime oldDetTime = currentDetTime;
  while (!violatedPtrs.empty() &&
         (options.tabuLim.get() == 1 ||
          stats.TABUDETTIME < options.tabuLim.get() * std::max(options.basetime.get(), currentDetTime))) {
    assert(violatedPtrs.empty() == violatedQueue.empty());
    quit::checkInterrupt();
    changeds.clear();
    CRef cr = violatedQueue.back();
    assert(violatedPtrs.count(cr));
    Constr& c = ca[cr];
    assert(!c.isSatisfiedByTabu(tabuSol));
    Lit* tabuLits = c.tabuLits();
    int high = c.nTabuLits();
    int low = 0;
    while (low < high && !c.isSatisfiedByTabu(tabuSol)) {
      int idx = aux::getRand(low, high);
      Lit l = tabuLits[idx];
      Var v = toVar(l);
      if (isUnit(getLevel(), l) || isUnit(getLevel(), -l)) {
        --c.nTabuLits();
        --high;
        std::swap(tabuLits[idx], tabuLits[high]);
        std::swap(tabuLits[high], tabuLits[c.nTabuLits()]);
      } else if (tabuSol[v] == l) {
        std::swap(tabuLits[idx], tabuLits[low]);
        ++low;
      } else if (ranks[v] > cutoff) {
        --high;
        std::swap(tabuLits[idx], tabuLits[high]);
      } else {
        flipTabu(l);
        std::swap(tabuLits[low], tabuLits[idx]);
        ++low;
        changeds.push_back(l);
      }
    }
    assert(c.isSatisfiedByTabu(tabuSol) || high == low);
    high = c.nTabuLits();
    while (!c.isSatisfiedByTabu(tabuSol)) {
      int idx = aux::getRand(low, high);
      Lit l = tabuLits[idx];
      assert(!isUnit(getLevel(), l));
      assert(!isUnit(getLevel(), -l));
      assert(tabuSol[toVar(l)] != l);
      cutoff = std::max(cutoff, ranks[toVar(l)]);
      flipTabu(l);
      std::swap(tabuLits[low], tabuLits[idx]);
      ++low;
      changeds.push_back(l);
    }
    assert(c.isSatisfiedByTabu(tabuSol));
    assert(!violatedPtrs.count(cr));

    oldDetTime = currentDetTime;
    currentDetTime = stats.getDetTime();
    stats.TABUDETTIME += currentDetTime - oldDetTime;
  }
  if (violatedPtrs.empty()) {
    lastSol.resize(getNbVars() + 1);
    lastSol[0] = 0;
    for (Var v = 1; v <= getNbVars(); ++v) lastSol[v] = isOrig(v) ? tabuSol[v] : 0;
    return true;
  }
  return false;
}

void Solver::flipTabu(Lit l) {
  ++stats.TABUFLIPS;
  Var v = toVar(l);
  assert(tabuSol[v] == -l);
  assert(!isUnit(getLevel(), -l));  // no flipping back unit lits
  assert(ranks[v] <= cutoff);
  tabuSol[v] = l;
  ranks[v] = next;
  ++next;
  for (const std::pair<const CRef, int>& cri : lit2cons[l]) {
    CRef cr = cri.first;
    Constr& c = ca[cr];
    c.increaseTabuSlack(cri.second);
    if (!c.isSatisfiedByTabu(tabuSol)) {
      assert(violatedPtrs.count(cr));
      continue;
    }
    eraseFromTabu(cr);
  }
  for (const std::pair<const CRef, int>& cri : lit2cons[-l]) {
    CRef cr = cri.first;
    Constr& c = ca[cr];
    c.decreaseTabuSlack(cri.second);
    if (c.isSatisfiedByTabu(tabuSol)) {
      assert(!violatedPtrs.count(cr));
      continue;
    }
    if (!violatedPtrs.count(cr)) {
      addToTabu(cr);
    }
  }
  assert(tabuSol[v] == l);
}

void Solver::phaseToTabu() {
  for (Var v = 1; v <= getNbVars(); ++v) {
    if (!isOrig(v)) continue;
    Lit l = tabuSol[v];
    assert(l != 0);
    assert(!isUnit(getLevel(), -l));
    if (!isUnit(getLevel(), l) && freeHeur.getPhase(v) != l) {
      cutoff = ranks[toVar(l)];
      flipTabu(-l);
    }
  }
}

void Solver::lastSolToPhase() {
  for (Var v = 1; v <= getNbVars(); ++v) {
    if (!isOrig(v)) continue;
    freeHeur.setPhase(v, lastSol[v]);
  }
}

void Solver::ranksToAct() {
  // TODO: refactor to VMTF activity structure
  //  ActValV nbConstrs = constraints.size();
  //  for (Var v = 1; v <= getNbVars(); ++v) {
  //    if (!isOrig(v)) continue;
  //    freeHeur.activity[v] = std::max(cutoff, ranks[v]) + (adj[v].size() + adj[-v].size()) / nbConstrs;
  //    cgHeur.activity[v] = freeHeur.activity[v];
  //  }
  //  freeHeur.heap.recalculate();
  //  freeHeur.v_vsids_inc = next;
  //  cgHeur.heap.recalculate();
  //  cgHeur.v_vsids_inc = next;
}

}  // namespace xct
