/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2024 Jo Devriendt, Nonfiction Software

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

  bigint maxVal = obj->getCutoffVal();
  if (maxVal <= static_cast<bigint>(limitAbs<int, long long>())) {  // TODO: try to internalize this check in ConstrExp
    Ce32 o = solver.global.cePools.take32();
    obj->copyTo(o);
    return std::make_shared<Optimization<int, long long>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<long long, int128>())) {
    Ce64 o = solver.global.cePools.take64();
    obj->copyTo(o);
    return std::make_shared<Optimization<long long, int128>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int128>())) {
    Ce96 o = solver.global.cePools.take96();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int128>>(o, solver, offs, assumps);
  } else if (maxVal <= static_cast<bigint>(limitAbs<int128, int256>())) {
    Ce128 o = solver.global.cePools.take128();
    obj->copyTo(o);
    return std::make_shared<Optimization<int128, int256>>(o, solver, offs, assumps);
  } else {
    CeArb o = solver.global.cePools.takeArb();
    obj->copyTo(o);
    return std::make_shared<Optimization<bigint, bigint>>(o, solver, offs, assumps);
  }
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(const CePtr<SMALL, LARGE>& obj, Solver& s, const bigint& os,
                                         const IntSet& assumps)
    : OptimizationSuper(s, os, assumps),
      origObj(obj),
      lower_bound(0),
      upper_bound(obj->absCoeffSum() + 1),
      lastUpperBound(ID_Undef),
      boundingVal(0),
      boundingVar(0) {
  assert(origObj->getDegree() == 0);
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
void Optimization<SMALL, LARGE>::boundObjByLastSol() {
  if (!solver.foundSolution()) throw InvalidArgument("No solution to add objective bound.");
  const LitVec& sol = solver.getLastSolution();

  upper_bound = -origObj->getRhs();
  for (Var v : origObj->getVars()) upper_bound += sol[v] > 0 ? origObj->coefs[v] : 0;
  printObjBounds();

  CePtr<SMALL, LARGE> aux = global.cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  aux->orig = Origin::UPPERBOUND;
  std::pair<ID, ID> res = solver.addConstraint(aux);
  lastUpperBound = res.second;
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::run(bool optimize, double timeout) {
  try {
    solver.presolve();  // will run only once, but also short-circuits (throws UnsatEncounter) when unsat was reached
  } catch (const UnsatEncounter& ue) {
    return SolveState::UNSAT;
  }

  while (true) {
    if (timeout != 0 && global.stats.getRunTime() > timeout) return SolveState::TIMEOUT;
    // NOTE: it's possible that upper_bound < lower_bound, since at the point of optimality, the objective-improving
    // constraint yields UNSAT, at which case core-guided search can derive any constraint.
    StatNum current_time = global.stats.getDetTime();

    if (optimize && lower_bound < upper_bound &&
        (global.options.optRatio.get() >= 1 ||
         global.stats.DETTIMEASSUMP <
             global.options.optRatio.get() * (global.stats.DETTIMEFREE + global.stats.DETTIMEASSUMP))) {
      boundBottomUp();
      std::vector<Lit> assumps = assumptions.getKeys();
      assumps.push_back(-boundingVar);
      solver.setAssumptions(assumps);
    } else {
      solver.setAssumptions(assumptions.getKeys());
    }

    SolveState reply;
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

    if (reply == SolveState::SAT) {
      assert(solver.foundSolution());
      ++global.stats.NSOLS;
      if (optimize) {
        boundObjByLastSol();
        solver.clearAssumptions();
      }
      return SolveState::SAT;
    } else if (reply == SolveState::INCONSISTENT) {
      assert(!solver.getAssumptions().isEmpty());
      ++global.stats.NCORES;
      if (solver.getAssumptions().size() > assumptions.size()) {
        if (solver.lastCore->falsifiedBy(assumptions)) {
          solver.clearAssumptions();
          return SolveState::INCONSISTENT;
        } else {
          lower_bound = boundingVal + 1;
          solver.addUnitConstraint(boundingVar, Origin::COREGUIDED);
          solver.clearAssumptions();
          printObjBounds();
        }
      } else {
        assert(solver.getAssumptions().size() == assumptions.size());  // no coreguided assumptions
        assert(solver.lastCore->falsifiedBy(assumptions));
        return SolveState::INCONSISTENT;
      }
    } else {
      assert(reply == SolveState::INPROCESSED || reply == SolveState::UNSAT);
      if (global.options.printCsvData) {
        global.stats.printCsvLine(static_cast<StatNum>(lower_bound), static_cast<StatNum>(upper_bound));
      }
      return reply;
    }
  }
}

template <typename SMALL, typename LARGE>
SolveState Optimization<SMALL, LARGE>::runFull(bool optimize, double timeout) {
  SolveState result = SolveState::INPROCESSED;
  while (result == SolveState::INPROCESSED || (result == SolveState::SAT && optimize)) {
    result = run(optimize, timeout);
  }
  return result;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::boundBottomUp() {
  assert(lower_bound < upper_bound);
  LARGE bnd = lower_bound + (upper_bound - lower_bound) / global.options.optPrecision.get();
  assert(bnd < upper_bound);
  assert(bnd >= lower_bound);
  if (boundingVar == 0 || bnd != boundingVal) {
    boundingVal = bnd;
    CeArb bound = global.cePools.takeArb();
    origObj->copyTo(bound);
    assert(bound->getDegree() == 0);
    bound->addRhs(boundingVal);  // objective must be at least middle
    bound->invert();             // objective must be at most middle
    boundingVar = solver.addVar(false);
    bound->addLhs(bound->getDegree(), boundingVar);  // ~boundingVar enables bisect constraint
    bound->orig = Origin::COREGUIDED;
    solver.addConstraint(bound);
  }
}

template class Optimization<int, long long>;
template class Optimization<long long, int128>;
template class Optimization<int128, int128>;
template class Optimization<int128, int256>;
template class Optimization<bigint, bigint>;

}  // namespace xct
