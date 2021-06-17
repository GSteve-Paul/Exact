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

#pragma once

#include <memory>
#include "Constr.hpp"
#include "Heuristic.hpp"
#include "IntSet.hpp"
#include "LpSolver.hpp"
#include "Options.hpp"
#include "parsing.hpp"
#include "typedefs.hpp"

namespace rs {

struct Logger;

enum class SolveState { SAT, UNSAT, INCONSISTENT, INPROCESSED };
enum class AMODetectState { FAILED, FOUNDUNIT, SUCCESS };

class Solver {
  friend class LpSolver;
  friend struct Constr;
  friend struct Clause;
  friend struct Cardinality;
  template <typename CF, typename DG>
  friend struct Counting;
  template <typename CF, typename DG>
  friend struct Watched;
  template <typename CF, typename DG>
  friend struct CountingSafe;
  template <typename CF, typename DG>
  friend struct WatchedSafe;

  // ---------------------------------------------------------------------
  // Members

 public:
  parsing::ILP ilp;
  std::shared_ptr<Logger> logger;
  std::vector<Lit> lastSol = {0};
  bool foundSolution() const { return getNbOrigVars() == 0 || lastSol.size() > 1; }
  CeSuper lastCore;
  bigint bestObjSoFar = 0;
  ratio getBestObjSoFar() const { return static_cast<ratio>(bestObjSoFar) / ilp.objmult; }
  // TODO: base this method on original objective function of ILP
  CeArb objective;
  bool hasObjective() const { return objective->nVars() > 0; }
  int maxSatVars = -1;

 private:
  int n;
  int orig_n;
  ID crefID = ID_Trivial;

  ConstraintAllocator ca;
  Heuristic freeHeur;
  Heuristic cgHeur;
  Heuristic* heur = &freeHeur;

  std::vector<CRef> constraints;  // row-based view
  std::unordered_map<ID, CRef> external;
  std::vector<std::unordered_map<CRef, int>> _lit2cons;  // column-based view, int is index of literal in CRef
  std::vector<std::unordered_map<CRef, int>>::iterator lit2cons;
  int lastRemoveSatisfiedsTrail = 0;
  std::unordered_multimap<Lit, Lit> binaryImplicants;  // l implies multimap[l]
  std::vector<int> _lit2consOldSize;
  std::vector<int>::iterator lit2consOldSize;

  std::vector<std::vector<Watch>> _adj;
  std::vector<std::vector<Watch>>::iterator adj;
  std::vector<int> _level;
  IntVecIt level;  // TODO: make position, level, contiguous memory for better cache efficiency.
  std::vector<int> position;
  std::vector<Lit> trail;
  std::vector<int> trail_lim;
  std::vector<CRef> reason;
  int qhead = 0;  // for unit propagation

  std::vector<int> assumptions_lim;
  IntSet assumptions;

  bool firstRun = true;
  std::shared_ptr<LpSolver> lpSolver;

  long long nconfl_to_reduce;
  long long nconfl_to_restart;

 public:
  Solver();
  ~Solver();
  void init();  // call after having read options

  int getNbVars() const { return n; }
  void setNbVars(int nvars, bool orig);
  int getNbOrigVars() const { return orig_n; }

  const IntVecIt& getLevel() const { return level; }
  const std::vector<int>& getPos() const { return position; }
  const Heuristic& getHeuristic() const { return *heur; }
  int decisionLevel() const { return trail_lim.size(); }
  int assumptionLevel() const { return assumptions_lim.size() - 1; }

  [[nodiscard]] std::pair<ID, ID> addConstraint(const CeSuper& c,
                                                Origin orig);  // result: formula line id, processed id
  [[nodiscard]] std::pair<ID, ID> addConstraint(const ConstrSimpleSuper& c,
                                                Origin orig);  // result: formula line id, processed id
  void addUnitConstraint(Lit l, Origin orig);
  template <typename T>
  void addConstraintChecked(const T& c, Origin orig) {
    // NOTE: logging of the inconsistency happened in addInputConstraint
    if (addConstraint(c, orig).second == ID_Unsat) quit::exit_SUCCESS(*this);
  }
  void dropExternal(ID id, bool erasable, bool forceDelete);
  int getNbConstraints() const { return constraints.size(); }
  CeSuper getIthConstraint(int i) const;
  const std::vector<CRef>& getRawConstraints() const { return constraints; }
  const ConstraintAllocator& getCA() const { return ca; }
  bool hasPureCnf() const;

  void setAssumptions(const std::vector<Lit>& assumps);
  void clearAssumptions();
  const IntSet& getAssumptions() const { return assumptions; }
  bool hasAssumptions() const { return !assumptions.isEmpty(); }
  bool assumptionsClashWithUnits() const;

  int getNbUnits() const;
  std::vector<Lit> getUnits() const;
  const std::vector<Lit>& getLastSolution() const;

  /**
   * @return SolveState:
   * 	UNSAT if root inconsistency detected
   * 	SAT if satisfying assignment found
   * 	    this->lastSol contains the satisfying assignment
   * 	INCONSISTENT if no solution extending assumptions exists
   * 	    this->lastCore is an implied constraint falsified by the assumptions,
   * 	    unless this->lastCore is a CeNull, which implies assumptionsClashWithUnits.
   * 	    Note that assumptionsClashWithUnits may still hold when this->lastCore is not a CeNull.
   * 	INPROCESSING if solver just finished a cleanup phase
   */
  // TODO: use a coroutine / yield instead of a SolveAnswer return value
  SolveState solve();

  bool checkSAT(const std::vector<Lit>& assignment);

 private:
  // ---------------------------------------------------------------------
  // Trail manipulation

  void enqueueUnit(Lit l, Var v, CRef r);
  void uncheckedEnqueue(Lit l, CRef r);
  void undoOne(bool updateHeur = true);
  void backjumpTo(int lvl, bool updateHeur = true);
  void decide(Lit l);
  void propagate(Lit l, CRef r);
  bool probe(Lit l);
  /**
   * Unit propagation with watched literals.
   * @post: all constraints have been checked for propagation under trail[0..qhead[
   * @return: true if inconsistency is detected, false otherwise. The inconsistency is stored in confl->
   */
  CeSuper runPropagation(bool onlyUnitPropagation);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  CeSuper analyze(const CeSuper& confl);
  void minimize(const CeSuper& conflict);
  void extractCore(const CeSuper& confl, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  CRef attachConstraint(const CeSuper& constraint, bool locked);
  void learnConstraint(const CeSuper& c, Origin orig);
  std::pair<ID, ID> addInputConstraint(const CeSuper& ce);
  void removeConstraint(const CRef& cr, bool override = false);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect();
  void reduceDB();

  // ---------------------------------------------------------------------
  // Restarts

  static double luby(double y, int i);

  // ---------------------------------------------------------------------
  // Inprocessing
  void presolve();
  void inProcess();
  void removeSatisfiedNonImpliedsAtRoot();
  void derivePureLits();
  void dominanceBreaking();
  void rebuildLit2Cons();

  Var lastRestartNext = 0;
  void probeRestart(Lit next);

  AMODetectState detectAtMostOne(Lit seed, std::unordered_set<Lit>& considered, std::vector<Lit>& previousProbe);
  std::unordered_set<uint64_t> atMostOneHashes;
  void runAtMostOneDetection();

  // ---------------------------------------------------------------------
  // Tabu search

  TabuRank next = 1;            // rank of the next literal to flip
  TabuRank cutoff = 0;          // all less than or equal to the cutoff can be flipped
  std::vector<TabuRank> ranks;  // Var to rank
  std::vector<Lit> tabuSol;

  std::list<CRef> violatedQueue;
  std::unordered_map<CRef, std::list<CRef>::const_iterator> violatedPtrs;

  void addToTabu(const CRef& cr);
  void eraseFromTabu(const CRef& cr);
  void rebuildTabu();
  void flipTabu(Lit l);

 public:
  bool runTabuOnce();
  int getTabuViolatedSize() {
    assert(violatedQueue.size() == violatedPtrs.size());
    return violatedPtrs.size();
  }
  void phaseToTabu();
  void lastSolToPhase();
  void ranksToAct();
};

}  // namespace rs
