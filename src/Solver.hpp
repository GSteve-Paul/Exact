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

#pragma once

#include <memory>
#include "Options.hpp"
#include "constraints/Constr.hpp"
#include "datastructures/Heuristic.hpp"
#include "datastructures/IntMap.hpp"
#include "datastructures/IntSet.hpp"
#include "parsing.hpp"
#include "propagation/Equalities.hpp"
#include "propagation/Implications.hpp"
#include "propagation/LpSolver.hpp"
#include "typedefs.hpp"

namespace xct {

class ILP;

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
  friend class Propagator;
  friend class Equalities;
  friend class Implications;

  // ---------------------------------------------------------------------
  // Members

 public:
  std::vector<Lit> lastSol = {0};
  bool foundSolution() const;
  CeSuper lastCore;
  CeSuper lastGlobalDual;
  IntSet objectiveLits;

 private:
  ILP& ilp;
  int n;
  std::vector<bool> isorig;

  ConstraintAllocator ca;
  Heuristic freeHeur;
  Heuristic cgHeur;
  Heuristic* heur = &freeHeur;

  std::vector<CRef> constraints;  // row-based view
  std::unordered_map<ID, CRef> external;
  IntMap<std::unordered_map<CRef, int>> lit2cons;  // column-based view, int is index of literal in CRef
  int lastRemoveSatisfiedsTrail = 0;
  std::unordered_multimap<Lit, Lit> binaryImplicants;  // l implies multimap[l]
  IntMap<int> lit2consOldSize;

  IntMap<std::vector<Watch>> adj;
  IntMap<int> level;  // TODO: make position, level, contiguous memory for better cache efficiency.
  std::vector<int> position;
  std::vector<Lit> trail;
  std::vector<int> trail_lim;
  std::vector<CRef> reason;
  int qhead = 0;  // for unit propagation

  std::vector<int> assumptions_lim;
  IntSet assumptions;

  std::shared_ptr<LpSolver> lpSolver;

  Equalities equalities;
  Implications implications;

  long long nconfl_to_reduce;
  long long nconfl_to_restart;

  CeSuper getAnalysisCE(const CeSuper& conflict) const;

 public:
  Solver(ILP& i);
  ~Solver();
  void init(const CeArb& obj);

  int getNbVars() const { return n; }
  void setNbVars(int nvars, bool orig);
  bool isOrig(Var v) const {
    assert(v > 0);
    return isorig[v];
  }

  Options& getOptions();
  Stats& getStats();
  const IntMap<int>& getLevel() const { return level; }
  const std::vector<int>& getPos() const { return position; }
  Equalities& getEqualities() { return equalities; }
  Implications& getImplications() { return implications; }
  const Heuristic& getHeuristic() const { return *heur; }

  int decisionLevel() const { return trail_lim.size(); }
  int assumptionLevel() const { return assumptions_lim.size() - 1; }

  // result: formula line id, processed id
  [[nodiscard]] std::pair<ID, ID> addConstraint(const CeSuper& c, Origin orig);
  [[nodiscard]] std::pair<ID, ID> addConstraint(const ConstrSimpleSuper& c, Origin orig);
  [[nodiscard]] ID addUnitConstraint(Lit l, Origin orig);
  template <typename T>
  void addConstraintUnchecked(const T& c, Origin orig) {
    // NOTE: logging of the inconsistency happened in addInputConstraint
    [[maybe_unused]] auto [_, id] = addConstraint(c, orig);
    assert(id != ID_Unsat);  // use regular addConstraint if it could be an inconsistency
  }
  [[nodiscard]] std::pair<ID, ID> invalidateLastSol(const std::vector<Var>& vars);

  void dropExternal(ID id, bool erasable, bool forceDelete);
  int getNbConstraints() const { return constraints.size(); }
  CeSuper getIthConstraint(int i) const;
  const std::vector<CRef>& getRawConstraints() const { return constraints; }
  const ConstraintAllocator& getCA() const { return ca; }

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
  [[nodiscard]] SolveState solve();

  bool checkSAT(const std::vector<Lit>& assignment);

 private:
  // ---------------------------------------------------------------------
  // Trail manipulation

  void enqueueUnit(Lit l, Var v, CRef r);
  void uncheckedEnqueue(Lit l, CRef r);
  void undoOne();
  void backjumpTo(int lvl);
  void decide(Lit l);
  void propagate(Lit l, CRef r);
  [[nodiscard]] State probe(Lit l, bool deriveImplications);
  /**
   * Unit propagation with watched literals.
   * @post: all constraints have been checked for propagation under trail[0..qhead[
   * @return: true if inconsistency is detected, false otherwise. The inconsistency is stored in confl
   */
  // TODO: don't return actual conflict, but analyze it internally? Won't work because core extraction is necessary
  [[nodiscard]] std::pair<CeSuper, State> runDatabasePropagation();
  [[nodiscard]] std::pair<CeSuper, State> runPropagation();
  [[nodiscard]] std::pair<CeSuper, State> runPropagationWithLP();
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  [[nodiscard]] CeSuper analyze(const CeSuper& confl);
  void minimize(const CeSuper& conflict);
  [[nodiscard]] State extractCore(const CeSuper& confl, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  [[nodiscard]] CRef attachConstraint(const CeSuper& constraint,
                                      bool locked);  // returns CRef_Unsat in case of inconsistency
  [[nodiscard]] ID learnConstraint(const CeSuper& c, Origin orig);
  [[nodiscard]] ID learnUnitConstraint(Lit l, Origin orig, ID id);
  [[nodiscard]] ID learnClause(const std::vector<Lit>& lits, Origin orig, ID id);
  std::pair<ID, ID> addInputConstraint(const CeSuper& ce);
  void removeConstraint(const CRef& cr, bool override = false);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect();
  State reduceDB();

  // ---------------------------------------------------------------------
  // Restarts

  static double luby(double y, int i);

  // ---------------------------------------------------------------------
  // Inprocessing
 public:
  [[nodiscard]] std::pair<State, CeSuper> presolve();

 private:
  [[nodiscard]] std::pair<State, CeSuper> inProcess();
  void removeSatisfiedNonImpliedsAtRoot();
  void derivePureLits();
  void dominanceBreaking();
  void rebuildLit2Cons();

  Var lastRestartNext = 0;
  [[nodiscard]] State probeRestart(Lit next);

  [[nodiscard]] State detectAtMostOne(Lit seed, std::unordered_set<Lit>& considered, std::vector<Lit>& previousProbe);
  std::unordered_map<uint64_t, unsigned int> atMostOneHashes;  // maps to size of at-most-one
  [[nodiscard]] State runAtMostOneDetection();

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

}  // namespace xct
