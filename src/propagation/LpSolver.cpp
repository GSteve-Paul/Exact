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

#include "LpSolver.hpp"
#include <queue>
#include "../Optimization.hpp"

namespace xct {

#if WITHSOPLEX

CandidateCut::CandidateCut(const CeSuper& in, const std::vector<double>& sol) {
  assert(in->isSaturated());
  in->saturateAndFixOverflowRational(sol);
  in->toSimple()->copyTo(simpcons);
  // NOTE: simpcons is already in var-normal form
  initialize(sol);
}

CandidateCut::CandidateCut(const Constr& in, CRef cref, const std::vector<double>& sol, ConstrExpPools& pools)
    : cr(cref) {
  assert(in.degree() > 0);
  CeSuper tmp = in.toExpanded(pools);
  tmp->saturateAndFixOverflowRational(sol);
  if (tmp->isTautology()) {
    return;
  }
  tmp->toSimple()->copyTo(simpcons);
  // NOTE: simpcons is already in var-normal form
  initialize(sol);
  assert(isValid(cr));
}

void CandidateCut::initialize(const std::vector<double>& sol) {
  std::sort(simpcons.terms.begin(), simpcons.terms.end(),
            [](const Term64& t1, const Term64& t2) { return t1.l < t2.l; });
  assert(norm == 1);
  norm = 0;
  for (const Term64& p : simpcons.terms) norm += aux::toDouble(p.c) * aux::toDouble(p.c);
  norm = std::sqrt(norm);
  ratSlack = -aux::toDouble(simpcons.rhs);
  for (Term64& p : simpcons.terms) {
    assert(p.l > 0);  // simpcons is in var-normal form
    ratSlack += aux::toDouble(p.c) * sol[p.l];
  }
  assert(norm >= 0);
  if (norm == 0) norm = 1;
  ratSlack /= norm;
}

// @pre: simpcons is ordered and norm is calculated
double CandidateCut::cosOfAngleTo(const CandidateCut& other) const {
  assert(norm != 0);
  assert(other.norm != 0);
  double cos = 0;
  int i = 0;
  int j = 0;
  while (i < (int)simpcons.size() && j < (int)other.simpcons.size()) {
    int x = simpcons.terms[i].l;
    int y = other.simpcons.terms[j].l;
    if (x < y)
      ++i;
    else if (x > y)
      ++j;
    else {  // x==y
      cos += aux::toDouble(simpcons.terms[i].c) * aux::toDouble(other.simpcons.terms[j].c);
      ++i;
      ++j;
    }
  }
  return cos / (norm * other.norm);
}

std::ostream& operator<<(std::ostream& o, const CandidateCut& cc) {
  return o << cc.simpcons << " norm " << cc.norm << " ratSlack " << cc.ratSlack;
}

LpSolver::LpSolver(ILP& i) : ilp(i), solver(i.getSolver()) {
  assert(INFTY == lp.realParam(lp.INFTY));

  if (options.verbosity.get() > 1) std::cout << "c Initializing LP" << std::endl;
  setNbVariables(solver.getNbVars() + 1);
  lp.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_ONLYREAL);
  lp.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_REAL);
  lp.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_REAL);
  lp.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_OFF);
  lp.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
  lp.setIntParam(soplex::SoPlex::VERBOSITY, options.verbosity.get());
  lp.setRandomSeed(0);

  // add two empty rows for objective bound constraints
  while (row2data.size() < 2) {
    soplex::DSVectorReal row(0);
    lp.addRowReal(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, 0));
    row2data.emplace_back(ID_Trivial, false);
  }

  // add all formula constraints
  // TODO: nonImplied constraints?
  solver.removeSatisfiedNonImpliedsAtRoot();
  for (CRef cr : solver.constraints) {
    Constr& c = solver.ca[cr];
    if (c.getOrigin() == Origin::FORMULA && !c.isMarkedForDelete()) {
      addConstraint(cr, false);
    }
  }

  soplex::DVectorReal objective;
  objective.reDim(getNbVariables());  // NOTE: automatically set to zero
  if (ilp.getObjective().getLhs().empty()) {
    for (int v = 1; v < getNbVariables(); ++v) objective[v] = 1;  // add default objective function
  } else {
    CeArb o = cePools.takeArb();
    ilp.getObjective().toConstrExp(o, true);
    o->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
    o->removeEqualities(solver.getEqualities(), false);
    for (Var v : o->getVars()) {
      objective[v] = aux::toDouble(o->coefs[v]);
    }
  }
  lp.changeObjReal(objective);

  if (options.verbosity.get() > 1) std::cout << "c Finished initializing LP" << std::endl;
}

void LpSolver::setNbVariables(int n) {
  if (n <= getNbVariables()) return;
  soplex::LPColSetReal allCols;
  allCols.reMax(n - getNbVariables());
  soplex::DSVectorReal dummycol(0);
  for (Var v = getNbVariables(); v < n; ++v) {
    allCols.add(soplex::LPColReal(0, dummycol, 1, 0));
  }
  lp.addColsReal(allCols);

  lpSol.reDim(n);
  lpSolution.resize(n, 0);
  lowerBounds.reDim(n);
  upperBounds.reDim(n);
  assert(getNbVariables() == n);
}

int LpSolver::getNbVariables() const { return lp.numCols(); }
int LpSolver::getNbRows() const { return lp.numRows(); }

CeSuper LpSolver::createLinearCombinationFarkas(soplex::DVectorReal& mults) {
  double scale = getScaleFactor(mults, true);
  if (scale == 0) return CeNull();
  assert(scale > 0);

  Ce128 out = cePools.take128();
  for (int r = 0; r < mults.dim(); ++r) {
    int128 factor = aux::cast<int128, double>(mults[r] * scale);
    if (factor <= 0) continue;
    assert(lp.lhsReal(r) != INFTY);
    Ce64 ce = rowToConstraint(r);
    stats.NLPADDEDLITERALS += ce->nVars();
    out->addUp(ce, factor);
  }
  out->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  assert(out->hasNoZeroes());
  out->weakenSmalls(aux::toDouble(out->absCoeffSum()) / out->nVars() * options.lpIntolerance.get());
  out->removeZeroes();
  out->saturateAndFixOverflow(solver.getLevel(), options.bitsOverflow.get(), options.bitsReduced.get(), 0);
  return out;
}

CandidateCut LpSolver::createLinearCombinationGomory(soplex::DVectorReal& mults) {
  double scale = getScaleFactor(mults, false);
  if (scale == 0) return CandidateCut();
  assert(scale > 0);
  Ce128 lcc = cePools.take128();

  std::vector<std::pair<int128, int>> slacks;
  for (int r = 0; r < mults.dim(); ++r) {
    int128 factor = aux::cast<int128, double>(mults[r] * scale);
    if (factor == 0) continue;
    Ce64 ce = rowToConstraint(r);
    if (factor < 0) ce->invert();
    stats.NLPADDEDLITERALS += ce->nVars();
    lcc->addUp(ce, aux::abs(factor));
    slacks.emplace_back(-factor, r);
  }

  int256 b = lcc->getRhs();
  for (Var v : lcc->getVars())
    if (lpSolution[v] > 0.5) b -= lcc->coefs[v];
  if (b == 0) {
    return CandidateCut();
  }

  assert(scale > 0);
  int128 divisor = aux::cast<int128, double>(std::ceil(scale));
  while ((b % divisor) == 0) ++divisor;
  lcc->applyMIR(divisor, [&](Var v) -> Lit { return lpSolution[v] <= 0.5 ? v : -v; });

  // round up the slack variables MIR style and cancel out the slack variables
  int128 bmodd = aux::mod_safe(b, divisor);
  for (auto& slk : slacks) {
    int128 factor = bmodd * aux::floordiv_safe(slk.first, divisor) + std::min(aux::mod_safe(slk.first, divisor), bmodd);
    // NOTE: MIR style rounding does not increase the coefficient
    if (factor == 0) continue;
    Ce64 ce = rowToConstraint(slk.second);
    if (factor < 0) ce->invert();
    stats.NLPADDEDLITERALS += ce->nVars();
    lcc->addUp(ce, aux::abs(factor));
  }
  if (lcc->plogger) {
    lcc->plogger->logAssumption(lcc);
  }
  // TODO: fix logging for Gomory cuts

  lcc->removeUnitsAndZeroes(solver.getLevel(), solver.getPos());
  lcc->saturate(true, false);
  if (lcc->isTautology())
    lcc->reset(false);
  else {
    assert(lcc->hasNoZeroes());
    lcc->weakenSmalls(aux::toDouble(lcc->absCoeffSum()) / lcc->nVars() * options.lpIntolerance.get());
  }
  CandidateCut result(lcc, lpSolution);
  return result;
}

void LpSolver::constructGomoryCandidates() {
  std::vector<int> indices;
  indices.resize(getNbRows());
  lp.getBasisInd(indices.data());

  assert(lpSlackSolution.dim() == getNbRows());
  std::vector<std::pair<double, int>> fracrowvec;
  for (int row = 0; row < getNbRows(); ++row) {
    quit::checkInterrupt();
    double fractionality = 0;
    if (indices[row] >= 0) {  // basic original variable / column
      assert(indices[row] < (int)lpSolution.size());
      fractionality = nonIntegrality(lpSolution[indices[row]]);
    } else {  // basic slack variable / row
      assert(-indices[row] - 1 < lpSlackSolution.dim());
      fractionality = nonIntegrality(lpSlackSolution[-indices[row] - 1]);
    }
    assert(fractionality >= 0);
    if (fractionality > 0) fracrowvec.emplace_back(fractionality, row);
  }
  std::priority_queue<std::pair<double, int>> fracrows(std::less<std::pair<double, int>>(), fracrowvec);

  [[maybe_unused]] double last = 0.5;
  for (int i = 0; i < options.lpGomoryCutLimit.get() && !fracrows.empty(); ++i) {
    assert(last >= fracrows.top().first);
    last = fracrows.top().first;
    int row = fracrows.top().second;
    fracrows.pop();

    assert(lpMultipliers.dim() == getNbRows());
    lpMultipliers.clear();
    lp.getBasisInverseRowReal(row, lpMultipliers.get_ptr());
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    if (candidateCuts.back().ratSlack >= -options.lpIntolerance.get()) candidateCuts.pop_back();
    for (int j = 0; j < lpMultipliers.dim(); ++j) lpMultipliers[j] = -lpMultipliers[j];
    candidateCuts.push_back(createLinearCombinationGomory(lpMultipliers));
    if (candidateCuts.back().ratSlack >= -options.lpIntolerance.get()) candidateCuts.pop_back();
  }
}

void LpSolver::constructLearnedCandidates() {
  for (CRef cr : solver.constraints) {
    quit::checkInterrupt();
    const Constr& c = solver.ca[cr];
    if (isLearned(c.getOrigin())) {
      bool containsNewVars = false;
      for (unsigned int i = 0; i < c.size && !containsNewVars; ++i) {
        containsNewVars = toVar(c.lit(i)) >= getNbVariables();
        assert((toVar(c.lit(i)) > solver.getNbOrigVars()) == containsNewVars);
        // for now, getNbVariables() == solver.getNbOrigVars().nbOrigVars+1
      }
      if (containsNewVars) continue;
      candidateCuts.emplace_back(c, cr, lpSolution, cePools);
      if (candidateCuts.back().ratSlack >= -options.lpIntolerance.get()) candidateCuts.pop_back();
    }
  }
}

State LpSolver::addFilteredCuts() {
  for ([[maybe_unused]] const CandidateCut& cc : candidateCuts) {
    assert(cc.norm != 0);
  }
  std::sort(candidateCuts.begin(), candidateCuts.end(), [](const CandidateCut& x1, const CandidateCut& x2) {
    return x1.ratSlack > x2.ratSlack || (x1.ratSlack == x2.ratSlack && x1.simpcons.size() < x2.simpcons.size());
  });

  // filter the candidate cuts
  std::vector<int> keptCuts;  // indices
  for (unsigned int i = 0; i < candidateCuts.size(); ++i) {
    bool parallel = false;
    for (unsigned int j = 0; j < keptCuts.size() && !parallel; ++j) {
      quit::checkInterrupt();
      parallel = candidateCuts[keptCuts[j]].cosOfAngleTo(candidateCuts[i]) > options.lpMaxCutCos.get();
    }
    if (!parallel) keptCuts.push_back(i);
  }

  for (int i : keptCuts) {
    CandidateCut& cc = candidateCuts[i];
    CeSuper ce = cc.simpcons.toExpanded(cePools);
    ce->postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true);
    assert(ce->fitsInDouble());
    assert(!ce->isTautology());
    if (cc.cr == CRef_Undef) {  // Gomory cut
      ID res = aux::timeCall<ID>([&] { return solver.learnConstraint(ce, Origin::GOMORY); }, stats.LEARNTIME);
      if (res == ID_Unsat) return State::UNSAT;
    } else {  // learned cut
      ++stats.NLPLEARNEDCUTS;
    }
    addConstraint(ce, true);
  }

  return State::SUCCESS;
}

void LpSolver::pruneCuts() {
  assert(getNbRows() == (int)row2data.size());
  lpMultipliers.clear();
  if (!lp.getDual(lpMultipliers)) return;
  for (int r = 0; r < getNbRows(); ++r)
    if (row2data[r].removable && lpMultipliers[r] == 0) {
      ++stats.NLPDELETEDCUTS;
      toRemove.push_back(r);
    }
}

// NOTE: it is possible that mults are negative (e.g., when calculating Gomory cuts)
double LpSolver::getScaleFactor(soplex::DVectorReal& mults, bool removeNegatives) {
  double largest = 0;
  int nonzeros = 0;
  for (int i = 0; i < mults.dim(); ++i) {
    if (std::isnan(mults[i]) || std::isinf(mults[i]) || (removeNegatives && mults[i] < 0)) mults[i] = 0;
    largest = std::max(aux::abs(mults[i]), largest);
    nonzeros += mults[i] == 0;
  }
  if (largest == 0) return 0;
  assert(nonzeros > 0);
  return maxMult / nonzeros / largest;
}

Ce64 LpSolver::rowToConstraint(int row) {
  Ce64 ce = cePools.take64();
  double rhs = lp.lhsReal(row);
  assert(aux::abs(rhs) != INFTY);
  assert(validVal(rhs));
  ce->addRhs((long long)rhs);

  lpRow.clear();
  lp.getRowVectorReal(row, lpRow);
  for (int i = 0; i < lpRow.size(); ++i) {
    const soplex::Nonzero<double>& el = lpRow.element(i);
    assert(validVal(el.val));
    assert(el.val != 0);
    ce->addLhs((long long)el.val, el.idx);
  }
  if (ce->plogger) ce->resetBuffer(row2data[row].id);
  return ce;
}

LpStatus LpSolver::checkFeasibility(bool inProcessing) {
  if (options.lpTimeRatio.get() == 1) {
    lp.setIntParam(soplex::SoPlex::ITERLIMIT, -1);  // no pivot limit
  } else {
    long double nlptime = stats.getNonLpDetTime();
    long double lptime = stats.getLpDetTime();
    assert(options.lpTimeRatio.get() != 0);
    if (lptime == 1 || lptime < options.lpTimeRatio.get() * (lptime + nlptime)) {
      double limit = options.lpPivotBudget.get() * lpPivotMult;
      limit = std::min<double>(limit, std::numeric_limits<int>::max());
      lp.setIntParam(soplex::SoPlex::ITERLIMIT, static_cast<int>(limit));
    } else {
      return LpStatus::PIVOTLIMIT;  // time ratio exceeded
    }
  }
  if (logger) logger->logComment("Checking LP");
  madeInternalCall = !inProcessing;
  flushConstraints();

  // Set the  LP's bounds based on the current trail
  for (Var v = 1; v < getNbVariables(); ++v) {
    lowerBounds[v] = isTrue(solver.getLevel(), v);
    upperBounds[v] = !isFalse(solver.getLevel(), v);
  }
  lp.changeBoundsReal(lowerBounds, upperBounds);

  // Run the LP
  soplex::SPxSolver::Status stat;
  stat = lp.optimize();
  ++stats.NLPCALLS;
  int pivots = lp.numIterations();
  stats.NLPPIVOTS += pivots;
  stats.NLPOPERATIONS += pivots * (long long)lp.numNonzeros();
  stats.LPSOLVETIME += lp.solveTime();
  stats.NLPNOPIVOT += pivots == 0;

  if (options.verbosity.get() > 1)
    std::cout << "c " << (inProcessing ? "root" : "internal") << " LP status: " << stat << std::endl;
  assert(stat != soplex::SPxSolver::Status::NO_PROBLEM);
  assert(stat <= soplex::SPxSolver::Status::OPTIMAL_UNSCALED_VIOLATIONS);
  assert(stat >= soplex::SPxSolver::Status::ERROR);

  if (stat == soplex::SPxSolver::Status::ABORT_ITER) {
    lpPivotMult *= 2;  // increase pivot budget when calling the LP solver
    return LpStatus::PIVOTLIMIT;
  }

  if (stat == soplex::SPxSolver::Status::OPTIMAL) {
    ++stats.NLPOPTIMAL;
    if (pivots != 0) {
      if (options.lpLearnDuals && lp.getDual(lpMultipliers)) {
        CeSuper confl = createLinearCombinationFarkas(lpMultipliers);
        if (confl) {
          ID res = aux::timeCall<ID>([&] { return solver.learnConstraint(confl, Origin::DUAL); }, stats.LEARNTIME);
          if (res == ID_Unsat) return LpStatus::UNSAT;
        }
      } else {
        ++stats.NLPNODUAL;
        resetBasis();
      }
    }
    if (!lp.hasSol()) {
      ++stats.NLPNOPRIMAL;
      resetBasis();
    }
    return LpStatus::OPTIMAL;
  }

  if (stat == soplex::SPxSolver::Status::ABORT_CYCLING) {
    ++stats.NLPCYCLING;
    resetBasis();
    return LpStatus::UNDETERMINED;
  }
  if (stat == soplex::SPxSolver::Status::SINGULAR) {
    ++stats.NLPSINGULAR;
    resetBasis();
    return LpStatus::UNDETERMINED;
  }
  if (stat != soplex::SPxSolver::Status::INFEASIBLE) {
    ++stats.NLPOTHER;
    resetBasis();
    return LpStatus::UNDETERMINED;
  }

  // Infeasible LP :)
  ++stats.NLPINFEAS;

  // To prove that we have an inconsistency, let's build the Farkas proof
  if (!lp.getDualFarkas(lpMultipliers)) {
    ++stats.NLPNOFARKAS;
    resetBasis();
    return LpStatus::UNDETERMINED;
  }

  CeSuper confl = createLinearCombinationFarkas(lpMultipliers);
  if (confl) {
    ID res = aux::timeCall<ID>([&] { return solver.learnConstraint(confl, Origin::FARKAS); }, stats.LEARNTIME);
    if (res == ID_Unsat) return LpStatus::UNSAT;
  }
  return LpStatus::INFEASIBLE;
}

State LpSolver::inProcess() {
  solver.backjumpTo(0);
  LpStatus lpstat = aux::timeCall<LpStatus>([&] { return checkFeasibility(true); }, stats.LPTOTALTIME);
  if (lpstat == LpStatus::UNSAT) return State::UNSAT;
  if (lpstat != LpStatus::OPTIMAL)
    return State::SUCCESS;  // Any unsatisfiability will be handled by adding the Farkas constraint
  if (!lp.hasSol()) return State::FAIL;
  lp.getPrimal(lpSol);
  assert(lpSol.dim() == (int)lpSolution.size());
  for (int i = 0; i < lpSol.dim(); ++i) lpSolution[i] = lpSol[i];
  lp.getSlacksReal(lpSlackSolution);
  assert(solver.getNbVars() + 1 >= getNbVariables());
  for (Var v = 1; v < getNbVariables(); ++v) {
    solver.freeHeur.setPhase(v, (lpSolution[v] <= 0.5) ? -v : v);
  }
  if (options.verbosity.get() > 0) {
    aux::prettyPrint(std::cout << "c rational objective ", lp.objValueReal()) << std::endl;
  }
  candidateCuts.clear();
  if (logger && (options.lpGomoryCuts || options.lpLearnedCuts)) logger->logComment("cutting");
  if (options.lpLearnedCuts) constructLearnedCandidates();  // first to avoid adding gomory cuts twice
  if (options.lpGomoryCuts) constructGomoryCandidates();
  if (addFilteredCuts() == State::UNSAT) return State::UNSAT;
  pruneCuts();
  return State::SUCCESS;
}

void LpSolver::resetBasis() {
  ++stats.NLPRESETBASIS;
  lp.clearBasis();  // and hope next iteration works fine
}

void LpSolver::convertConstraint(const ConstrSimple64& c, soplex::DSVectorReal& row, double& rhs) {
  assert(row.max() >= (int)c.size());
  for (auto& t : c.terms) {
    if (t.c == 0) continue;
    assert(t.l > 0);
    assert(t.l < lp.numColsReal());
    assert(t.c < INFLPINT);
    row.add(t.l, t.c);
  }
  rhs = aux::toDouble(c.rhs);
  assert(validVal(rhs));
}

void LpSolver::addConstraint(const CeSuper& c, bool removable, bool upperbound, bool lowerbound) {
  assert(!upperbound || c->orig == Origin::UPPERBOUND);
  assert(!lowerbound || c->orig == Origin::LOWERBOUND);
  c->saturateAndFixOverflowRational(lpSolution);
  // TODO: fix below kind of logger check
  ID id = logger ? logger->logProofLineWithInfo(c, "LP") : ++Logger::last_proofID;
  if (upperbound || lowerbound) {
    boundsToAdd[lowerbound].id = id;
    c->toSimple()->copyTo(boundsToAdd[lowerbound].cs);
  } else {
    toAdd[id] = {ConstrSimple64(), removable};
    c->toSimple()->copyTo(toAdd[id].cs);
  }
}

void LpSolver::addConstraint(CRef cr, bool removable, bool upperbound, bool lowerbound) {
  assert(isValid(cr));
  addConstraint(solver.ca[cr].toExpanded(cePools), removable, upperbound, lowerbound);
}

void LpSolver::flushConstraints() {
  if (!toRemove.empty()) {  // first remove rows
    std::vector<int> rowsToRemove(getNbRows(), 0);
    for (int row : toRemove) {
      stats.NLPDELETEDROWS += (rowsToRemove[row] == 0);
      assert(row < (int)rowsToRemove.size());
      rowsToRemove[row] = -1;
    }
    lp.removeRowsReal(rowsToRemove.data());  // TODO: use other removeRowsReal method?
    for (int r = 0; r < (int)rowsToRemove.size(); ++r) {
      int newrow = rowsToRemove[r];
      if (newrow < 0 || newrow == r) continue;
      row2data[newrow] = row2data[r];
    }
    row2data.resize(getNbRows());
    toRemove.clear();
  }

  if (!toAdd.empty()) {  // then add rows
    soplex::LPRowSetReal rowsToAdd;
    rowsToAdd.reMax(toAdd.size());
    row2data.reserve(row2data.size() + toAdd.size());
    for (auto& p : toAdd) {
      double rhs;
      soplex::DSVectorReal row(p.second.cs.size());
      convertConstraint(p.second.cs, row, rhs);
      rowsToAdd.add(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs));
      row2data.emplace_back(p.first, p.second.removable);
      ++stats.NLPADDEDROWS;
    }
    lp.addRowsReal(rowsToAdd);
    toAdd.clear();
  }

  for (int i = 0; i < 2; ++i) {
    if (boundsToAdd[i].id == row2data[i].id) continue;
    double rhs;
    soplex::DSVectorReal row(boundsToAdd[i].cs.size());
    convertConstraint(boundsToAdd[i].cs, row, rhs);
    lp.changeRowReal(i, soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, rhs));
    row2data[i] = {boundsToAdd[i].id, false};  // so upper bound resides in row[0]
  }

  lpSlackSolution.reDim(getNbRows());
  lpMultipliers.reDim(getNbRows());
  assert((int)row2data.size() == getNbRows());
}

#endif  // WITHSOPLEX

}  // namespace xct