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
#include "Constr.hpp"
#include "aux.hpp"
#include "globals.hpp"

namespace rs {

// ---------------------------------------------------------------------
// Initialization

Solver::Solver() : n(0), orig_n(0), assumptions_lim({0}), nconfl_to_reduce(0), nconfl_to_restart(0) {
  ca.capacity(1024 * 1024);  // 4MB
  objective = cePools.takeArb();
}

Solver::~Solver() {
  for (CRef cr : constraints) {
    ca[cr].freeUp();
  }
}

void Solver::setNbVars(int nvars, bool orig) {
  assert(nvars > 0);
  assert(nvars < INF);
  if (nvars <= n) return;
  aux::resizeIntMap(_adj, adj, nvars, resize_factor, {});
  aux::resizeIntMap(_level, level, nvars, resize_factor, INF);
  position.resize(nvars + 1, INF);
  reason.resize(nvars + 1, CRef_Undef);
  freeHeur.resize(nvars + 1);
  cgHeur.resize(nvars + 1);
  cePools.resize(nvars + 1);
  // if (lpSolver) lpSolver->setNbVariables(nvars + 1); // Currently, LP solver only reasons on formula constraints
  n = nvars;
  if (orig) {
    ranks.resize(nvars + 1, 0);
    tabuSol.resize(nvars + 1);
    for (Var v = orig_n + 1; v <= nvars; ++v) {
      tabuSol[v] = -v;
    }
    orig_n = nvars;
    stats.NORIGVARS.z = nvars;
    stats.NAUXVARS.z = 0;
    aux::resizeIntMap(_lit2cons, lit2cons, nvars, resize_factor, {});
    aux::resizeIntMap(_lit2consOldSize, lit2consOldSize, nvars, resize_factor, std::numeric_limits<int>::max());
  } else {
    stats.NAUXVARS.z = n - orig_n;
  }
}

void Solver::init() {
  if (!options.proofLog.get().empty()) logger = std::make_shared<Logger>(options.proofLog.get());
  cePools.initializeLogging(logger);
  objective->stopLogging();
  nconfl_to_restart = options.lubyMult.get();
  nconfl_to_reduce += 10 * options.dbCleanInc.get();
}

// ---------------------------------------------------------------------
// Assignment manipulation

void Solver::enqueueUnit(Lit l, Var v, CRef r) {
  assert(toVar(l) == v);
  assert(stats.NUNITS == trail.size());
  ++stats.NUNITS;
  reason[v] = CRef_Undef;  // no need to keep track of reasons for unit literals
  if (logger) {
    ca[r].toExpanded(cePools)->logUnit(level, position, v, stats);
    assert(logger->unitIDs.size() == trail.size() + 1);
  }
  if (options.tabuLim.get() != 0 && v <= getNbOrigVars() && tabuSol[v] != l) {
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

void Solver::undoOne(bool updateHeur) {
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
  if (updateHeur) heur->undoOne(v, l);
  if (isDecided(reason, v)) {
    assert(!trail_lim.empty());
    assert(trail_lim.back() == (int)trail.size());
    trail_lim.pop_back();
    if (decisionLevel() < assumptionLevel()) {
      assumptions_lim.pop_back();
    }
  }
}

void Solver::backjumpTo(int lvl, bool updateHeur) {
  assert(lvl >= 0);
  while (decisionLevel() > lvl) undoOne(updateHeur);
}

void Solver::decide(Lit l) {
  ++stats.NDECIDE;
  trail_lim.push_back(trail.size());
  uncheckedEnqueue(l, CRef_Undef);
}

void Solver::propagate(Lit l, CRef r) {
  assert(r != CRef_Undef);
  ++stats.NPROP;
  uncheckedEnqueue(l, r);
}

bool Solver::probe(Lit l) {
  assert(decisionLevel() == 0);
  assert(isUnknown(getPos(), l));
  ++stats.NPROBINGS;
  decide(l);
  CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(false); }, stats.PROPTIME);
  if (confl) {
    CeSuper analyzed = aux::timeCall<CeSuper>([&] { return analyze(confl); }, stats.CATIME);
    aux::timeCallVoid([&] { learnConstraint(analyzed, Origin::LEARNED); }, stats.LEARNTIME);
  }
  return decisionLevel() != 0;
}

/**
 * Unit propagation with watched literals.
 * @post: all watches up to trail[qhead] have been propagated
 */
CeSuper Solver::runPropagation(bool runLP) {
  while (qhead < (int)trail.size()) {
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
          return result;
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
    if (runLP && lpSolver) {
      aux::timeCall<LpStatus>([&] { return lpSolver->checkFeasibility(false); }, stats.LPTOTALTIME);
      // NOTE: calling LP solver may increase the propagations on the trail due to added constraints
    }
  }
  assert(qhead == (int)trail.size());
  return CeNull();
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
  if (bitsOverflow == 0 || bitsOverflow > conflLimit128) {
    CeArb confl = cePools.takeArb();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit96) {
    Ce128 confl = cePools.take128();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit64) {
    Ce96 confl = cePools.take96();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit32) {
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
  if (logger) logger->logComment("Analyze", stats);
  assert(conflict->hasNegativeSlack(level));
  conflict->removeUnitsAndZeroes(level, position);
  conflict->saturateAndFixOverflow(getLevel(), options.bitsOverflow.get(), options.bitsReduced.get(), 0);

  CeSuper confl = getAnalysisCE(conflict, options.bitsOverflow.get(), cePools);
  conflict->reset(false);

  IntSet& actSet = isPool.take();  // will hold the literals that need their activity bumped
  for (Var v : confl->getVars()) {
    if (options.bumpLits) {
      actSet.add(confl->getLit(v));
    } else if (!options.bumpOnlyFalse || isFalse(level, confl->getLit(v))) {
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
    minimize(confl, actSet);
    if (confl->isAssertingBefore(level, decisionLevel()) != AssertionStatus::ASSERTING) goto resolve;
  }

  heur->vBumpActivity(actSet.getKeys());
  isPool.release(actSet);

  assert(confl->hasNegativeSlack(level));
  return confl;
}

void Solver::minimize(const CeSuper& conflict, IntSet& actSet) {
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
    int lbd = aux::timeCall<bool>([&] { return reasonC.subsumeWith(conflict, -l, *this, actSet, saturatedLits); },
                                  stats.MINTIME);
    if (lbd > 0) {
      reasonC.decreaseLBD(lbd);
      reasonC.fixEncountered();
    }
    if (saturatedLits.isEmpty()) break;
  }
  conflict->removeZeroes();  // remove weakened literals
  isPool.release(saturatedLits);
}

void Solver::extractCore(const CeSuper& conflict, Lit l_assump) {
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
  heur->vBumpActivity(actSet.getKeys());
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
  aux::timeCallVoid([&] { learnConstraint(lastCore, Origin::LEARNED); },
                    stats.LEARNTIME);  // NOTE: takes care of inconsistency
  backjumpTo(0);
  lastCore->postProcess(getLevel(), getPos(), getHeuristic(), true, stats);
  if (!lastCore->hasNegativeSlack(assumptions)) {  // apparently unit clauses were propagated during learnConstraint
    lastCore.makeNull();
  }
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

  CRef cr = constraint->toConstr(ca, locked, logger ? constraint->logProofLineWithInfo("Attach", stats) : ++crefID);
  Constr& c = ca[cr];
  c.initializeWatches(cr, *this);
  constraints.push_back(cr);
  if (usedInTabu(c.getOrigin())) {
    for (unsigned int i = 0; i < c.size; ++i) {
      Lit l = c.lit(i);
      assert(toVar(l) <= getNbOrigVars());
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
    atMostOneHashes.insert(hash);
  }

  Origin orig = c.getOrigin();
  bool learned = isLearned(orig);
  if (learned) {
    stats.LEARNEDLENGTHSUM += c.size;
    stats.LEARNEDDEGREESUM += c.degree();
    stats.LEARNEDSTRENGTHSUM += c.strength;
    stats.LEARNEDLBDSUM += c.lbd();
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
    CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(false); }, stats.PROPTIME);
    if (confl) {
      assert(confl->hasNegativeSlack(getLevel()));
      if (logger) confl->logInconsistency(level, position, stats);
      quit::exit_SUCCESS(*this);
    }
  }

  return cr;
}

/**
 * Adds c as a learned constraint with origin orig.
 * Backjumps to the level where c is no longer conflicting, as otherwise we might miss propagations.
 * If conflicting at level 0, calls quit::exit_SUCCESS.
 */
void Solver::learnConstraint(const CeSuper& c, Origin orig) {
  assert(c);
  assert(isLearned(orig));
  CeSuper learned = c->clone(cePools);
  learned->orig = orig;
  learned->removeUnitsAndZeroes(getLevel(), getPos());
  learned->saturateAndFixOverflow(getLevel(), options.bitsLearned.get(), options.bitsLearned.get(), 0);
  learned->sortInDecreasingCoefOrder(getHeuristic());
  auto [assertionLevel, isAsserting] = learned->getAssertionStatus(level, position);
  if (assertionLevel < 0) {
    backjumpTo(0);
    assert(learned->isInconsistency());
    if (logger) learned->logInconsistency(getLevel(), getPos(), stats);
    quit::exit_SUCCESS(*this);
  }
  backjumpTo(assertionLevel);
  assert(!learned->hasNegativeSlack(level));
  if (isAsserting) learned->heuristicWeakening(level, position, stats);
  learned->postProcess(getLevel(), getPos(), getHeuristic(), false, stats);
  assert(learned->isSaturated());
  if (!learned->isTautology()) {
    CRef cr = attachConstraint(learned, false);
    ca[cr].decreaseLBD(isAsserting ? learned->getLBD(level) : learned->nVars());
    // the LBD of non-asserting constraints is undefined, so we take a safe upper bound
  }
}

std::pair<ID, ID> Solver::addInputConstraint(const CeSuper& ce) {
  assert(isInput(ce->orig) || ce->orig == Origin::DETECTEDAMO);
  assert(decisionLevel() == 0);
  ID input = ID_Undef;
  if (logger) input = ce->logAsInput();
  ce->postProcess(getLevel(), getPos(), getHeuristic(), true, stats);
  if (ce->isTautology()) {
    return {input, ID_Undef};  // already satisfied.
  }

  if (ce->hasNegativeSlack(level)) {
    if (options.verbosity.get() > 0) {
      std::cout << "c Conflicting input constraint" << std::endl;
    }
    if (logger) ce->logInconsistency(level, position, stats);
    assert(decisionLevel() == 0);
    return {input, ID_Unsat};
  }

  CRef cr = attachConstraint(ce, true);
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

void Solver::addUnitConstraint(Lit l, Origin orig) {
  if (addConstraint(ConstrSimple32({{1, l}}, 1), orig).second == ID_Unsat) quit::exit_SUCCESS(*this);
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
      assert(toVar(l) <= getNbOrigVars());
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

bool Solver::hasPureCnf() const {
  // TODO: make this a dynamic check based on the constraints added to the constraint database?
  if (hasObjective() || (rs::options.lpTimeRatio.get() != 0 && rs::options.lpGomoryCuts)) return false;
  return std::all_of(constraints.cbegin(), constraints.cend(), [&](CRef cr) { return ca[cr].degree() == 1; });
}

// ---------------------------------------------------------------------
// Assumptions

void Solver::setAssumptions(const std::vector<Lit>& assumps) {
  clearAssumptions();
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
    if (toVar(l) > getNbOrigVars()) continue;
    units.push_back(l);
  }
  return units;
}

const std::vector<Lit>& Solver::getLastSolution() const { return lastSol; }

// ---------------------------------------------------------------------
// Garbage collection

void Solver::rebuildLit2Cons() {
  for (std::unordered_map<CRef, int>& col : _lit2cons) {
    col.clear();
  }
  for (const CRef& cr : constraints) {
    Constr& c = ca[cr];
    if (c.isMarkedForDelete() || !usedInTabu(c.getOrigin())) continue;
    for (unsigned int i = 0; i < c.size; ++i) {
      assert(toVar(c.lit(i)) <= getNbOrigVars());
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
void Solver::reduceDB() {
  backjumpTo(0);  // otherwise reason CRefs need to be taken care of
  std::vector<CRef> learnts;
  learnts.reserve(constraints.size() / 2);

  removeSatisfiedNonImpliedsAtRoot();
  for (const CRef& cr : constraints) {
    Constr& c = ca[cr];
    if (c.isMarkedForDelete() || c.isLocked() || external.count(c.id)) continue;
    assert(!usedInTabu(c.getOrigin()));
    if (c.isSatisfiedAtRoot(getLevel())) {
      ++stats.NSATISFIEDSREMOVED;
      removeConstraint(cr);
    } else if ((int)c.lbd() > options.dbSafeLBD.get()) {
      learnts.push_back(cr);  // Don't erase glue constraints
    }
  }

  nconfl_to_reduce += options.dbCleanInc.get();
  std::sort(learnts.begin(), learnts.end(), [&](CRef x, CRef y) {
    int res = (int)ca[x].lbd() - (int)ca[y].lbd();
    return res < 0 || (res == 0 && ca[x].strength > ca[y].strength);
  });
  for (size_t i = learnts.size() * options.dbKeptRatio.get(); i < learnts.size(); ++i) {
    removeConstraint(learnts[i]);
  }

  for (Lit l = -n; l <= n; ++l) {
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (ca[adj[l][i].cref].isMarkedForDelete()) {
        aux::swapErase(adj[l], i--);
      }
    }
  }

  std::vector<int> cardPoints;
  for (size_t i = learnts.size() / 2; i < learnts.size(); ++i) {
    Constr& c = ca[learnts[i]];
    if (!c.isClauseOrCard()) {
      CeSuper ce = c.toExpanded(cePools);
      ce->removeUnitsAndZeroes(getLevel(), getPos());
      assert(ce->getCardinalityDegree() > 0);
      ce->simplifyToCardinality(false, ce->getMaxStrengthCardinalityDegree(cardPoints));
      learnConstraint(ce, Origin::REDUCED);
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

void Solver::inProcess() {
  assert(decisionLevel() == 0);
  removeSatisfiedNonImpliedsAtRoot();
  if (options.pureLits) derivePureLits();
  removeSatisfiedNonImpliedsAtRoot();
  if (options.domBreakLim.get() != 0) dominanceBreaking();
  if (options.inpAMO.get() != 0) aux::timeCallVoid([&] { runAtMostOneDetection(); }, stats.ATMOSTONETIME);
    // TODO: timing methods should be done via wrapper methods

#if WITHSOPLEX
  if (firstRun && options.lpTimeRatio.get() > 0) {
    lpSolver = std::make_shared<LpSolver>(*this);
    aux::timeCallVoid([&] { lpSolver->inProcess(); }, stats.LPTOTALTIME);
  } else if (lpSolver && lpSolver->canInProcess()) {
    aux::timeCallVoid([&] { lpSolver->inProcess(); }, stats.LPTOTALTIME);
  }
#endif  // WITHSOPLEX
}

void Solver::presolve() {
  if (options.verbosity.get() > 0) std::cout << "c PRESOLVE" << std::endl;
  aux::timeCallVoid([&] { inProcess(); }, stats.INPROCESSTIME);
  firstRun = false;
}

void Solver::removeSatisfiedNonImpliedsAtRoot() {
  assert(decisionLevel() == 0);
  std::vector<CRef> toCheck;
  for (int i = lastRemoveSatisfiedsTrail; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (toVar(l) > getNbOrigVars()) continue;  // no column view for auxiliary variables for now
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
  for (Lit l = -getNbOrigVars(); l <= getNbOrigVars(); ++l) {  // NOTE: core-guided variables will not be eliminated
    quit::checkInterrupt();
    if (l != 0 && isUnknown(getPos(), l) && !objective->hasLit(l) && lit2cons[-l].empty()) {
      addUnitConstraint(l, Origin::PURE);
    }
  }
}

void Solver::dominanceBreaking() {
  std::unordered_set<Lit> inUnsaturatableConstraint;
  IntSet& tmpSet = isPool.take();
  IntSet& actSet = isPool.take();
  for (Lit l = -getNbOrigVars(); l <= getNbOrigVars(); ++l) {
    assert(tmpSet.isEmpty());
    if (l == 0 || isKnown(getPos(), l) || objective->hasLit(l)) continue;
    std::unordered_map<CRef, int>& col = lit2cons[-l];
    if (col.empty()) {
      addUnitConstraint(l, Origin::PURE);
      removeSatisfiedNonImpliedsAtRoot();
      continue;
    }
    if ((options.domBreakLim.get() != -1 && (int)col.size() >= options.domBreakLim.get()) ||
        (int)col.size() >= lit2consOldSize[-l] || inUnsaturatableConstraint.count(-l))
      continue;

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
        tmpSet.add(first->lit(i));
      }
    }
    tmpSet.remove(-l);  // if l is false, then we can not pick it to be true ;)
    auto range = binaryImplicants.equal_range(-l);
    for (auto it = range.first; it != range.second; ++it) {
      tmpSet.remove(-it->second);  // not interested in anything that already implies l
    }
    for (const std::pair<const CRef, int>& pr : col) {
      if (tmpSet.isEmpty()) break;
      Constr& c = ca[pr.first];
      unsigned int unsatIdx = c.getUnsaturatedIdx();
      if (unsatIdx == 0) {
        for (unsigned int i = 0; i < c.size; ++i) {
          inUnsaturatableConstraint.insert(c.lit(i));
        }
      }
      assert(actSet.isEmpty());
      for (unsigned int i = 0; i < unsatIdx; ++i) {
        quit::checkInterrupt();
        Lit ll = c.lit(i);
        if (tmpSet.has(ll)) actSet.add(ll);
      }
      tmpSet = actSet;
      actSet.clear();
    }
    if (tmpSet.isEmpty()) continue;

    // tmpSet contains the intersection of the saturating literals for all constraints,
    // so asserting any literal in tmpSet makes l pure,
    // so we can add all these binary implicants as dominance breakers.
    for (Lit ll : tmpSet.getKeys()) {
      binaryImplicants.insert({ll, l});
      binaryImplicants.insert({-l, -ll});
      addConstraintChecked(ConstrSimple32{{{1, l}, {1, -ll}}, 1}, Origin::DOMBREAKER);
    }
    tmpSet.clear();
  }
  isPool.release(tmpSet);
  isPool.release(actSet);
}

SolveState Solver::solve() {
  if (firstRun) presolve();
  bool runLP = false;
  while (true) {
    quit::checkInterrupt();
    CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(runLP); }, stats.PROPTIME);
    runLP = (bool)confl;
    if (confl) {
      assert(confl->hasNegativeSlack(level));
      heur->vDecayActivity();
      ++stats.NCONFL;
      nconfl_to_restart--;
      long long nconfl = static_cast<long long>(stats.NCONFL.z);
      if (nconfl % 1000 == 0 && options.verbosity.get() > 0) {
        std::cout << "c " << nconfl << " confls " << constraints.size() << " constrs "
                  << getNbVars() - (long long)stats.NUNITS.z << " vars" << std::endl;
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
          confl->logInconsistency(level, position, stats);
        }
        return SolveState::UNSAT;
      } else if (decisionLevel() > assumptionLevel()) {
        CeSuper analyzed = aux::timeCall<CeSuper>([&] { return analyze(confl); }, stats.CATIME);
        assert(analyzed);
        assert(analyzed->hasNegativeSlack(getLevel()));
        assert(analyzed->isSaturated());
        aux::timeCallVoid([&] { learnConstraint(analyzed, Origin::LEARNED); }, stats.LEARNTIME);
      } else {
        aux::timeCallVoid([&] { extractCore(confl); }, stats.CATIME);
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
      if (stats.NCONFL >= (stats.NCLEANUP + 1) * nconfl_to_reduce) {
        if (options.verbosity.get() > 0) std::cout << "c INPROCESSING" << std::endl;
        ++stats.NCLEANUP;
        aux::timeCallVoid([&] { reduceDB(); }, stats.CLEANUPTIME);
        while (stats.NCONFL >= stats.NCLEANUP * nconfl_to_reduce) nconfl_to_reduce += options.dbCleanInc.get();
        aux::timeCallVoid([&] { inProcess(); }, stats.INPROCESSTIME);
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
              aux::timeCallVoid([&] { extractCore(ca[reason[toVar(l)]].toExpanded(cePools), -l); }, stats.CATIME);
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
        next = heur->pickBranchLit(getPos());
      }
      if (next == 0) {
        assert((int)trail.size() == getNbVars());
        lastSol.resize(getNbOrigVars() + 1);
        lastSol[0] = 0;
        for (Var v = 1; v <= getNbOrigVars(); ++v) lastSol[v] = isTrue(level, v) ? v : -v;
        backjumpTo(0);
        return SolveState::SAT;
      }
      assert(next != 0);
      if (options.inpProbing && decisionLevel() == 0 && toVar(lastRestartNext) != toVar(next)) {
        aux::timeCallVoid([&] { probeRestart(next); }, stats.PROBETIME);
        assert(isKnown(getPos(), next));  // needed as next is popped from activity heap
      } else {
        decide(next);
      }
    }
  }
}

void Solver::probeRestart(Lit next) {
  lastRestartNext = toVar(next);
  int oldUnits = trail.size();
  if (probe(-next)) {
    IntSet& tmpSet = isPool.take();
    for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
      tmpSet.add(trail[i]);
    }
    backjumpTo(0, false);
    std::vector<Lit> newUnits;
    if (probe(next)) {
      for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
        Lit l = trail[i];
        if (tmpSet.has(l)) {
          newUnits.push_back(l);
        }
      }
      if (!newUnits.empty()) {
        backjumpTo(0, false);
        for (Lit l : newUnits) {
          assert(!isUnit(getLevel(), -l));
          if (!isUnit(getLevel(), l)) {
            addConstraintChecked(ConstrSimple32({{1, l}}, 1), Origin::PROBING);
          }
        }
      }
    }
    isPool.release(tmpSet);  // TODO: rename tmpSet, actSet to something more meaningful
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
}

AMODetectState Solver::detectAtMostOne(Lit seed, std::unordered_set<Lit>& considered, std::vector<Lit>& previousProbe) {
  assert(decisionLevel() == 0);
  if (considered.count(seed)) {
    return AMODetectState::FAILED;
  }
  std::vector<Lit> cardLits = {seed};
  std::vector<Lit> candidates = {};
  if (isKnown(getPos(), seed) || !probe(-seed)) return AMODetectState::FOUNDUNIT;

  // find candidates
  assert(decisionLevel() == 1);
  candidates.reserve(trail.size() - trail_lim[0]);
  for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
    candidates.push_back(trail[i]);
  }
  backjumpTo(0, false);

  if (!previousProbe.empty()) {
    IntSet& tmpSet = isPool.take();
    for (Lit l : previousProbe) {
      tmpSet.add(l);
    }
    for (Lit l : candidates) {
      if (tmpSet.has(l)) {
        addConstraintChecked(ConstrSimple32({{1, l}}, 1), Origin::PROBING);
      }
    }
    isPool.release(tmpSet);
  } else {
    previousProbe = candidates;
  }

  // check whether at least three of them form a clique
  while (candidates.size() > 1) {
    assert(decisionLevel() == 0);
    quit::checkInterrupt();
    for (int i = 1; i < (int)candidates.size(); ++i) {
      if (getHeuristic().getActivity(toVar(candidates[i])) > getHeuristic().getActivity(toVar(candidates[0]))) {
        std::swap(candidates[i], candidates[0]);
      }
    }
    Lit current = candidates[0];
    aux::swapErase(candidates, 0);
    IntSet& tmpSet = isPool.take();
    if (isKnown(getPos(), current) || !probe(-current)) {
      isPool.release(tmpSet);
      continue;
    }
    for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
      Lit l = trail[i];
      tmpSet.add(l);
    }
    backjumpTo(0, false);
    for (Lit l : cardLits) {
      if (tmpSet.has(-l)) {
        addConstraintChecked(ConstrSimple32({{1, current}}, 1), Origin::PROBING);
        isPool.release(tmpSet);
        continue;
      }
    }
    int candidatesLeft = 0;
    for (Lit l : candidates) {
      candidatesLeft += tmpSet.has(l);
    }
    if (candidatesLeft > 0) {
      cardLits.push_back(current);  // found an additional cardinality lit
      for (int i = 0; i < (int)candidates.size(); ++i) {
        if (!tmpSet.has(candidates[i])) {
          aux::swapErase(candidates, i--);
        }
      }
      assert(candidatesLeft == (int)candidates.size());
    }
    isPool.release(tmpSet);
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
    if (atMostOneHashes.count(hash)) return AMODetectState::FAILED;
    atMostOneHashes.insert(hash);
    ConstrSimple32 card{{}, (int)cardLits.size() - 1};
    for (Lit l : cardLits) {
      card.terms.push_back({1, l});
    }
    ++stats.ATMOSTONES;
    // learnConstraint(card.toExpanded(cePools), Origin::DETECTEDAMO);
    addConstraintChecked(card, Origin::DETECTEDAMO);  // TODO: add proof logging and add as a learned constraint
    return AMODetectState::SUCCESS;
  } else {
    return AMODetectState::FAILED;
  }
}

void Solver::runAtMostOneDetection() {
  assert(decisionLevel() == 0);
  int currentUnits = trail.size();
  long double currentDetTime = stats.getDetTime();
  long double oldDetTime = currentDetTime;
  std::vector<Var> readd;
  std::vector<Lit> previous;
  std::unordered_set<Lit> considered;
  Lit next = heur->pickBranchLit(getPos());
  readd.push_back(toVar(next));
  while (next != 0 &&
         (options.inpAMO.get() == 1 ||
          stats.ATMOSTONEDETTIME < options.inpAMO.get() * std::max(options.basetime.get(), currentDetTime))) {
    previous.clear();
    detectAtMostOne(-next, considered, previous);
    detectAtMostOne(next, considered, previous);
    next = heur->pickBranchLit(getPos());
    readd.push_back(toVar(next));
    oldDetTime = currentDetTime;
    currentDetTime = stats.getDetTime();
    stats.ATMOSTONEDETTIME += currentDetTime - oldDetTime;
  }
  for (Var v : readd) {
    heur->heap.insert(v);
  }
  stats.NATMOSTONEUNITS += trail.size() - currentUnits;
}

void Solver::addToTabu(const CRef& cr) {
  assert(usedInTabu(ca[cr].getOrigin()));
  assert(cr != CRef_Undef);
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
  long double currentDetTime = stats.getDetTime();
  long double oldDetTime = currentDetTime;
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

    IntSet& tmpSet = isPool.take();
    for (Lit l : changeds) {
      if (!tmpSet.has(toVar(l)) && !isUnit(getLevel(), l) && !isUnit(getLevel(), -l) && probe(l)) {
        // NOTE: l may have become unit by previous probing...
        for (int i = trail_lim[0] + 1; i < (int)trail.size(); ++i) {
          Lit ll = trail[i];
          Var vv = toVar(ll);
          if (vv <= getNbOrigVars()) {
            tmpSet.add(vv);
            if (tabuSol[vv] != ll) {
              cutoff = std::max(cutoff, ranks[vv]);
              flipTabu(ll);
            }
          }
        }
        backjumpTo(0, false);
      }
    }
    isPool.release(tmpSet);
    oldDetTime = currentDetTime;
    currentDetTime = stats.getDetTime();
    stats.TABUDETTIME += currentDetTime - oldDetTime;
  }
  if (violatedPtrs.empty()) {
    lastSol.resize(getNbOrigVars() + 1);
    lastSol[0] = 0;
    for (Var v = 1; v <= getNbOrigVars(); ++v) lastSol[v] = tabuSol[v];
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
  for (Var v = 1; v <= getNbOrigVars(); ++v) {
    Lit l = tabuSol[v];
    assert(!isUnit(getLevel(), -l));
    if (!isUnit(getLevel(), l) && freeHeur.getPhase(v) != l) {
      cutoff = ranks[toVar(l)];
      flipTabu(-l);
    }
  }
}

void Solver::lastSolToPhase() {
  for (Var v = 1; v <= getNbOrigVars(); ++v) {
    freeHeur.setPhase(v, lastSol[v]);
  }
}

void Solver::ranksToAct() {
  ActValV nbConstrs = constraints.size();
  for (Var v = 1; v <= getNbOrigVars(); ++v) {
    freeHeur.activity[v] = std::max(cutoff, ranks[v]) + (adj[v].size() + adj[-v].size()) / nbConstrs;
    cgHeur.activity[v] = freeHeur.activity[v];
  }
  freeHeur.heap.recalculate();
  freeHeur.v_vsids_inc = next;
  cgHeur.heap.recalculate();
  cgHeur.v_vsids_inc = next;
}

}  // namespace rs
