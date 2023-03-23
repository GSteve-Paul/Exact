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

#include "Constr.hpp"
#include "../Solver.hpp"

namespace xct {

Constr::Constr(ID i, Origin o, bool lkd, unsigned int lngth, float strngth)
    : id(i), strength(strngth), size(lngth), header{0, lkd, 0, (unsigned int)o, MAXLBD} {
  assert(strength <= 1);
  assert(strength > 0);
}

std::ostream& operator<<(std::ostream& o, const Constr& c) {
  for (unsigned int i = 0; i < c.size; ++i) {
    o << c.coef(i) << "x" << c.lit(i) << " ";
  }
  return o << ">= " << c.degree();
}

void Constr::fixEncountered(Stats& stats) const {  // TODO: better as method of Stats?
  const Origin o = getOrigin();
  stats.NENCFORMULA += o == Origin::FORMULA;
  stats.NENCDOMBREAKER += o == Origin::DOMBREAKER;
  stats.NENCLEARNED += o == Origin::LEARNED;
  stats.NENCBOUND += isBound(o);
  stats.NENCCOREGUIDED += o == Origin::COREGUIDED;
  stats.NLPENCGOMORY += o == Origin::GOMORY;
  stats.NLPENCDUAL += o == Origin::DUAL;
  stats.NLPENCFARKAS += o == Origin::FARKAS;
  stats.NENCDETECTEDAMO += o == Origin::DETECTEDAMO;
  stats.NENCREDUCED += o == Origin::REDUCED;
  stats.NENCEQ += o == Origin::EQUALITY;
  stats.NENCIMPL += o == Origin::IMPLICATION;
  ++stats.NRESOLVESTEPS;
}

void Clause::initializeWatches(CRef cr, Solver& solver) {
  auto& level = solver.level;
  auto& adj = solver.adj;

  unsigned int length = size;
  assert(length >= 1);
  if (length == 1) {
    assert(solver.decisionLevel() == 0);
    assert(isCorrectlyPropagating(solver, 0));
    solver.propagate(data[0], cr);
    return;
  }

  unsigned int watch = 0;
  for (unsigned int i = 0; i < length && watch <= 1; ++i) {
    Lit l = data[i];
    if (!isFalse(level, l)) {
      data[i] = data[watch];
      data[watch++] = l;
    }
  }
  assert(watch >= 1);  // we found enough watches to satisfy the constraint
  assert((watch == 1) == isFalse(level, data[1]));
  if (watch == 1) {
    assert(!isFalse(level, data[0]));
    if (!isTrue(level, data[0])) {
      assert(isCorrectlyPropagating(solver, 0));
      solver.propagate(data[0], cr);
    }
    for (unsigned int i = 2; i < length; ++i) {  // ensure last watch is last falsified literal
      Lit l = data[i];
      assert(isFalse(level, l));
      if (level[-l] > level[-data[1]]) {
        data[i] = data[1];
        data[1] = l;
      }
    }
  }
  for (unsigned int i = 0; i < 2; ++i) adj[data[i]].emplace_back(cr, data[1 - i] - INF);  // add blocked literal
}

WatchStatus Clause::checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, Stats& stats) {
  auto& level = solver.level;
  auto& adj = solver.adj;

  assert(idx < 0);
  assert(p == data[0] || p == data[1]);
  assert(size > 1);
  int widx = 0;
  Lit watch = data[0];
  Lit otherwatch = data[1];
  if (p == data[1]) {
    widx = 1;
    watch = data[1];
    otherwatch = data[0];
  }
  assert(p == watch);
  assert(p != otherwatch);
  if (isTrue(level, otherwatch)) {
    idx = otherwatch - INF;         // set new blocked literal
    return WatchStatus::KEEPWATCH;  // constraint is satisfied
  }

  const unsigned int length = size;
  for (unsigned int i = 2; i < length; ++i) {
    Lit l = data[i];
    if (!isFalse(level, l)) {
      unsigned int mid = i / 2 + 1;
      data[i] = data[mid];
      data[mid] = watch;
      data[widx] = l;
      adj[l].emplace_back(cr, otherwatch - INF);
      stats.NWATCHCHECKS += i - 1;
      return WatchStatus::DROPWATCH;
    }
  }
  stats.NWATCHCHECKS += length - 2;

  assert(isFalse(level, watch));
  for (unsigned int i = 2; i < length; ++i) assert(isFalse(level, data[i]));
  if (isFalse(level, otherwatch)) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  } else {
    assert(!isTrue(level, otherwatch));
    ++stats.NPROPCLAUSE;
    assert(isCorrectlyPropagating(solver, 1 - widx));
    solver.propagate(otherwatch, cr);
  }
  ++stats.NPROPCHECKS;
  return WatchStatus::KEEPWATCH;
}

int Clause::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(data, size, 1, id, l, solver.getLevel(), solver.getPos(), actSet);
}
int Clause::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(data, size, 1, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

CeSuper Clause::toExpanded(ConstrExpPools& cePools) const {
  Ce32 result = cePools.take32();
  result->addRhs(1);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(1, data[i]);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

bool Clause::isSatisfiedAtRoot(const IntMap<int>& level) const {
  for (int i = 0; i < (int)size; ++i) {
    if (isUnit(level, data[i])) return true;
  }
  return false;
}

bool Clause::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                             IntSetPool& isp) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i];
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  if (!isEquality) {
    IntSet& hasImplieds = isp.take();
    for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
      Lit l = data[i];
      if (implications.hasImplieds(l)) hasImplieds.add(-l);
    }
    if (!hasImplieds.isEmpty()) {
      for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
        if (hasImplieds.has(data[i])) {
          isp.release(hasImplieds);
          return true;
        }
      }
    }
    isp.release(hasImplieds);
  }
  return false;
}

void Cardinality::initializeWatches(CRef cr, Solver& solver) {
  assert(degr > 1);  // otherwise not a cardinality
  auto& level = solver.level;
  [[maybe_unused]] auto& position = solver.position;
  auto& adj = solver.adj;

  unsigned int length = size;
  if (degr >= length) {
    assert(solver.decisionLevel() == 0);
    for (unsigned int i = 0; i < length; ++i) {
      assert(isUnknown(position, data[i]));
      assert(isCorrectlyPropagating(solver, i));
      solver.propagate(data[i], cr);
    }
    return;
  }

  unsigned int watch = 0;
  for (unsigned int i = 0; i < length && watch <= degr; ++i) {
    Lit l = data[i];
    if (!isFalse(level, l)) {
      data[i] = data[watch];
      data[watch++] = l;
    }
  }
  assert(watch >= degr);  // we found enough watches to satisfy the constraint
  if (isFalse(level, data[degr])) {
    for (unsigned int i = 0; i < degr; ++i) {
      assert(!isFalse(level, data[i]));
      if (!isTrue(level, data[i])) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i], cr);
      }
    }
    for (unsigned int i = degr + 1; i < size; ++i) {  // ensure last watch is last falsified literal
      Lit l = data[i];
      assert(isFalse(level, l));
      if (level[-l] > level[-data[degr]]) {
        data[i] = data[degr];
        data[degr] = l;
      }
    }
  }
  for (unsigned int i = 0; i <= degr; ++i) adj[data[i]].emplace_back(cr, i);  // add watch index
}

WatchStatus Cardinality::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver, Stats& stats) {
  auto& level = solver.level;
  auto& adj = solver.adj;

  assert(idx >= 0);
  assert(idx < INF);
  assert(data[idx] == p);
  const unsigned int length = size;
  if (ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS.z;
    watchIdx = degr + 1;
  }
  assert(watchIdx > degr);
  stats.NWATCHCHECKS -= watchIdx;
  for (; watchIdx < length; ++watchIdx) {
    Lit l = data[watchIdx];
    if (!isFalse(level, l)) {
      unsigned int mid = (watchIdx + degr + 1) / 2;
      assert(mid <= watchIdx);
      assert(mid > degr);
      data[watchIdx] = data[mid];
      data[mid] = data[idx];
      data[idx] = l;
      adj[l].emplace_back(cr, idx);
      stats.NWATCHCHECKS += watchIdx + 1;
      return WatchStatus::DROPWATCH;
    }
  }
  stats.NWATCHCHECKS += watchIdx;
  assert(isFalse(level, data[idx]));
  for (unsigned int i = degr + 1; i < length; ++i) assert(isFalse(level, data[i]));
  for (int i = 0; i <= (int)degr; ++i)
    if (i != idx && isFalse(level, data[i])) {
      assert(isCorrectlyConflicting(solver));
      return WatchStatus::CONFLICTING;
    }
  int cardprops = 0;
  for (int i = 0; i <= (int)degr; ++i) {
    Lit l = data[i];
    if (i != idx && !isTrue(level, l)) {
      ++cardprops;
      assert(isCorrectlyPropagating(solver, i));
      solver.propagate(l, cr);
    }
  }
  stats.NPROPCHECKS += degr + 1;
  stats.NPROPCARD += cardprops;
  return WatchStatus::KEEPWATCH;
}

int Cardinality::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(data, size, degr, id, l, solver.getLevel(), solver.getPos(), actSet);
}
int Cardinality::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(data, size, degr, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

CeSuper Cardinality::toExpanded(ConstrExpPools& cePools) const {
  Ce32 result = cePools.take32();
  result->addRhs(degr);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(1, data[i]);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

bool Cardinality::isSatisfiedAtRoot(const IntMap<int>& level) const {
  int eval = -static_cast<int>(degr);
  for (int i = 0; i < (int)size && eval < 0; ++i) {
    eval += isUnit(level, data[i]);
  }
  return eval >= 0;
}

bool Cardinality::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications&, IntSetPool&) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i];
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  // NOTE: no saturated literals in a cardinality, so no need to check for self-subsumption
  return false;
}

template <typename CF, typename DG>
void Counting<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  slack = -degr;
  unsigned int length = size;
  for (unsigned int i = 0; i < length; ++i) {
    Lit l = data[i].l;
    adj[l].emplace_back(cr, i + INF);
    if (!isFalse(level, l) || position[toVar(l)] >= qhead) slack += data[i].c;
  }

  assert(slack >= 0);
  assert(hasCorrectSlack(solver));
  if (slack < data[0].c) {  // propagate
    for (unsigned int i = 0; i < length && data[i].c > slack; ++i)
      if (isUnknown(position, data[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i].l, cr);
      }
  }
}

template <typename CF, typename DG>
WatchStatus Counting<CF, DG>::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver,
                                                  Stats& stats) {
  auto& position = solver.position;

  assert(idx >= INF);
  assert(data[idx - INF].l == p);
  const unsigned int length = size;
  const CF& lrgstCf = data[0].c;
  const CF& c = data[idx - INF].c;

  slack -= c;
  assert(hasCorrectSlack(solver));

  if (slack < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  if (slack < lrgstCf) {
    if (ntrailpops < stats.NTRAILPOPS) {
      ntrailpops = stats.NTRAILPOPS.z;
      watchIdx = 0;
    }
    int countingprops = 0;
    stats.NPROPCHECKS -= watchIdx;
    for (; watchIdx < length && data[watchIdx].c > slack; ++watchIdx) {
      const Lit l = data[watchIdx].l;
      if (isUnknown(position, l)) {
        stats.NPROPCLAUSE += (degr == 1);
        stats.NPROPCARD += (degr != 1 && lrgstCf == 1);
        ++countingprops;
        assert(isCorrectlyPropagating(solver, watchIdx));
        solver.propagate(l, cr);
      }
    }
    stats.NPROPCHECKS += watchIdx;
    stats.NPROPCOUNTING += countingprops;
  }
  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void Counting<CF, DG>::undoFalsified(int i) {
  assert(i >= INF);
  slack += data[i - INF].c;
}

template <typename CF, typename DG>
int Counting<CF, DG>::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(data, size, degr, id, getOrigin(), l, solver.getLevel(), solver.getPos(), actSet);
}
template <typename CF, typename DG>
int Counting<CF, DG>::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(data, size, degr, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

template <typename CF, typename DG>
CePtr<CF, DG> Counting<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<CF, DG> result = cePools.take<CF, DG>();
  result->addRhs(degr);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(data[i].c, data[i].l);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

template <typename CF, typename DG>
CeSuper Counting<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool Counting<CF, DG>::isSatisfiedAtRoot(const IntMap<int>& level) const {
  DG eval = -degr;
  for (int i = 0; i < (int)size && eval < 0; ++i) {
    if (isUnit(level, data[i].l)) eval += data[i].c;
  }
  return eval >= 0;
}

template <typename CF, typename DG>
bool Counting<CF, DG>::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                                       IntSetPool& isp) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i].l;
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  if (!isEquality) {
    IntSet& hasImplieds = isp.take();
    for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
      Lit l = data[i].l;
      if (implications.hasImplieds(l)) hasImplieds.add(-l);
    }
    if (!hasImplieds.isEmpty()) {
      for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
        if (hasImplieds.has(data[i].l)) {
          isp.release(hasImplieds);
          return true;
        }
      }
    }
    isp.release(hasImplieds);
  }
  return false;
}

template <typename CF, typename DG>
void Watched<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  watchslack = -degr;
  unsigned int length = size;
  const CF lrgstCf = aux::abs(data[0].c);
  for (unsigned int i = 0; i < length && watchslack < lrgstCf; ++i) {
    Lit l = data[i].l;
    if (!isFalse(level, l) || position[toVar(l)] >= qhead) {
      assert(data[i].c > 0);
      watchslack += data[i].c;
      data[i].c = -data[i].c;
      adj[l].emplace_back(cr, i + INF);
    }
  }
  assert(watchslack >= 0);
  assert(hasCorrectSlack(solver));
  if (watchslack < lrgstCf) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(length);
    for (unsigned int i = 0; i < length; ++i)
      if (isFalse(level, data[i].l) && position[toVar(data[i].l)] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(), [&](unsigned int i1, unsigned int i2) {
      return position[toVar(data[i1].l)] > position[toVar(data[i2].l)];
    });
    DG diff = lrgstCf - watchslack;
    for (unsigned int i : falsifiedIdcs) {
      assert(data[i].c > 0);
      diff -= data[i].c;
      data[i].c = -data[i].c;
      adj[data[i].l].emplace_back(cr, i + INF);
      if (diff <= 0) break;
    }
    // perform initial propagation
    for (unsigned int i = 0; i < length && aux::abs(data[i].c) > watchslack; ++i)
      if (isUnknown(position, data[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i].l, cr);
      }
  }
}

template <typename CF, typename DG>
WatchStatus Watched<CF, DG>::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver,
                                                 Stats& stats) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;

  assert(idx >= INF);
  assert(data[idx - INF].l == p);
  const unsigned int length = size;
  const CF lrgstCf = aux::abs(data[0].c);
  CF& c = data[idx - INF].c;

  if (ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS.z;
    watchIdx = 0;
  }

  assert(c < 0);
  watchslack += c;
  if (watchslack - c >= lrgstCf) {  // look for new watches if previously, slack was at least lrgstCf
    stats.NWATCHCHECKS -= watchIdx;
    for (; watchIdx < length && watchslack < lrgstCf; ++watchIdx) {
      const CF& cf = data[watchIdx].c;
      const Lit l = data[watchIdx].l;
      if (cf > 0 && !isFalse(level, l)) {
        watchslack += cf;
        data[watchIdx].c = -cf;
        adj[l].emplace_back(cr, watchIdx + INF);
      }
    }  // NOTE: first innermost loop
    stats.NWATCHCHECKS += watchIdx;
    if (watchslack < lrgstCf) {
      assert(watchIdx == length);
      watchIdx = 0;
    }
  }  // else we did not find enough watches last time, so we can skip looking for them now

  assert(hasCorrectSlack(solver));
  assert(hasCorrectWatches(solver));

  if (watchslack >= lrgstCf) {
    c = -c;
    return WatchStatus::DROPWATCH;
  }
  if (watchslack < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  // keep the watch, check for propagation
  int watchprops = 0;
  stats.NPROPCHECKS -= watchIdx;
  for (; watchIdx < length && aux::abs(data[watchIdx].c) > watchslack; ++watchIdx) {
    const Lit l = data[watchIdx].l;
    if (isUnknown(position, l)) {
      stats.NPROPCLAUSE += (degr == 1);
      stats.NPROPCARD += (degr != 1 && lrgstCf == 1);
      ++watchprops;
      assert(isCorrectlyPropagating(solver, watchIdx));
      solver.propagate(l, cr);
    }  // NOTE: second innermost loop
  }
  stats.NPROPCHECKS += watchIdx;
  stats.NPROPWATCH += watchprops;
  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void Watched<CF, DG>::undoFalsified(int i) {
  assert(i >= INF);
  assert(data[i - INF].c < 0);
  watchslack -= data[i - INF].c;
}

template <typename CF, typename DG>
int Watched<CF, DG>::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(data, size, degr, id, getOrigin(), l, solver.getLevel(), solver.getPos(), actSet);
}
template <typename CF, typename DG>
int Watched<CF, DG>::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(data, size, degr, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

template <typename CF, typename DG>
CePtr<CF, DG> Watched<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<CF, DG> result = cePools.take<CF, DG>();
  result->addRhs(degr);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(aux::abs(data[i].c), data[i].l);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

template <typename CF, typename DG>
CeSuper Watched<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool Watched<CF, DG>::isSatisfiedAtRoot(const IntMap<int>& level) const {
  DG eval = -degr;
  for (int i = 0; i < (int)size && eval < 0; ++i) {
    if (isUnit(level, data[i].l)) eval += aux::abs(data[i].c);
  }
  return eval >= 0;
}

template <typename CF, typename DG>
bool Watched<CF, DG>::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                                      IntSetPool& isp) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i].l;
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  if (!isEquality) {
    IntSet& hasImplieds = isp.take();
    for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
      Lit l = data[i].l;
      if (implications.hasImplieds(l)) hasImplieds.add(-l);
    }
    if (!hasImplieds.isEmpty()) {
      for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
        if (hasImplieds.has(data[i].l)) {
          isp.release(hasImplieds);
          return true;
        }
      }
    }
    isp.release(hasImplieds);
  }
  return false;
}

template <typename CF, typename DG>
void CountingSafe<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  DG& slk = *slack;
  slk = -*degr;
  unsigned int length = size;
  for (unsigned int i = 0; i < length; ++i) {
    Lit l = terms[i].l;
    adj[l].emplace_back(cr, i + INF);
    if (!isFalse(level, l) || position[toVar(l)] >= qhead) slk += terms[i].c;
  }

  assert(slk >= 0);
  assert(hasCorrectSlack(solver));
  if (slk < terms[0].c) {  // propagate
    for (unsigned int i = 0; i < length && terms[i].c > slk; ++i) {
      Lit l = terms[i].l;
      if (isUnknown(position, l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(l, cr);
      }
    }
  }
}

template <typename CF, typename DG>
WatchStatus CountingSafe<CF, DG>::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver,
                                                      Stats& stats) {
  auto& position = solver.position;

  assert(idx >= INF);
  assert(terms[idx - INF].l == p);
  const unsigned int length = size;
  const CF& lrgstCf = terms[0].c;
  const CF& c = terms[idx - INF].c;

  DG& slk = *slack;
  slk -= c;
  assert(hasCorrectSlack(solver));

  if (slk < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  if (slk < lrgstCf) {
    if (ntrailpops < stats.NTRAILPOPS) {
      ntrailpops = stats.NTRAILPOPS.z;
      watchIdx = 0;
    }
    int countingprops = 0;
    stats.NPROPCHECKS -= watchIdx;
    for (; watchIdx < length && terms[watchIdx].c > slk; ++watchIdx) {
      const Lit l = terms[watchIdx].l;
      if (isUnknown(position, l)) {
        stats.NPROPCLAUSE += (*degr == 1);
        stats.NPROPCARD += (*degr != 1 && lrgstCf == 1);
        ++countingprops;
        assert(isCorrectlyPropagating(solver, watchIdx));
        solver.propagate(l, cr);
      }
    }
    stats.NPROPCHECKS += watchIdx;
    stats.NPROPCOUNTING += countingprops;
  }
  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void CountingSafe<CF, DG>::undoFalsified(int i) {
  assert(i >= INF);
  *slack += terms[i - INF].c;
}

template <typename CF, typename DG>
int CountingSafe<CF, DG>::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(terms, size, *degr, id, getOrigin(), l, solver.getLevel(), solver.getPos(), actSet);
}
template <typename CF, typename DG>
int CountingSafe<CF, DG>::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(terms, size, *degr, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

template <typename CF, typename DG>
CePtr<CF, DG> CountingSafe<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<CF, DG> result = cePools.take<CF, DG>();
  result->addRhs(*degr);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(terms[i].c, terms[i].l);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

template <typename CF, typename DG>
CeSuper CountingSafe<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool CountingSafe<CF, DG>::isSatisfiedAtRoot(const IntMap<int>& level) const {
  DG eval = -*degr;
  for (int i = 0; i < (int)size && eval < 0; ++i) {
    if (isUnit(level, terms[i].l)) eval += terms[i].c;
  }
  return eval >= 0;
}

template <typename CF, typename DG>
bool CountingSafe<CF, DG>::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                                           IntSetPool& isp) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = terms[i].l;
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  if (!isEquality) {
    IntSet& hasImplieds = isp.take();
    for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
      Lit l = terms[i].l;
      if (implications.hasImplieds(l)) hasImplieds.add(-l);
    }
    if (!hasImplieds.isEmpty()) {
      for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
        if (hasImplieds.has(terms[i].l)) {
          isp.release(hasImplieds);
          return true;
        }
      }
    }
    isp.release(hasImplieds);
  }
  return false;
}

template <typename CF, typename DG>
void WatchedSafe<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  DG& wslk = *watchslack;
  wslk = -*degr;
  unsigned int length = size;
  const CF lrgstCf = aux::abs(terms[0].c);
  for (unsigned int i = 0; i < length && wslk < lrgstCf; ++i) {
    Lit l = terms[i].l;
    if (!isFalse(level, l) || position[toVar(l)] >= qhead) {
      assert(terms[i].c > 0);
      wslk += terms[i].c;
      terms[i].c = -terms[i].c;
      adj[l].emplace_back(cr, i + INF);
    }
  }
  assert(wslk >= 0);
  assert(hasCorrectSlack(solver));
  if (wslk < lrgstCf) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(length);
    for (unsigned int i = 0; i < length; ++i)
      if (isFalse(level, terms[i].l) && position[toVar(terms[i].l)] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(), [&](unsigned int i1, unsigned int i2) {
      return position[toVar(terms[i1].l)] > position[toVar(terms[i2].l)];
    });
    DG diff = lrgstCf - wslk;
    for (unsigned int i : falsifiedIdcs) {
      assert(terms[i].c > 0);
      diff -= terms[i].c;
      terms[i].c = -terms[i].c;
      adj[terms[i].l].emplace_back(cr, i + INF);
      if (diff <= 0) break;
    }
    // perform initial propagation
    for (unsigned int i = 0; i < length && aux::abs(terms[i].c) > wslk; ++i)
      if (isUnknown(position, terms[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(terms[i].l, cr);
      }
  }
}

template <typename CF, typename DG>
WatchStatus WatchedSafe<CF, DG>::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver,
                                                     Stats& stats) {
  auto& level = solver.level;
  auto& position = solver.position;
  auto& adj = solver.adj;

  assert(idx >= INF);
  assert(terms[idx - INF].l == p);
  const unsigned int length = size;
  const CF lrgstCf = aux::abs(terms[0].c);
  CF& c = terms[idx - INF].c;

  if (ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS.z;
    watchIdx = 0;
  }

  assert(c < 0);
  DG& wslk = *watchslack;
  wslk += c;
  if (wslk - c >= lrgstCf) {  // look for new watches if previously, slack was at least lrgstCf
    stats.NWATCHCHECKS -= watchIdx;
    for (; watchIdx < length && wslk < lrgstCf; ++watchIdx) {
      const CF& cf = terms[watchIdx].c;
      const Lit l = terms[watchIdx].l;
      if (cf > 0 && !isFalse(level, l)) {
        wslk += cf;
        terms[watchIdx].c = -cf;
        adj[l].emplace_back(cr, watchIdx + INF);
      }
    }  // NOTE: first innermost loop
    stats.NWATCHCHECKS += watchIdx;
    if (wslk < lrgstCf) {
      assert(watchIdx == length);
      watchIdx = 0;
    }
  }  // else we did not find enough watches last time, so we can skip looking for them now

  assert(hasCorrectSlack(solver));
  assert(hasCorrectWatches(solver));

  if (wslk >= lrgstCf) {
    c = -c;
    return WatchStatus::DROPWATCH;
  }
  if (wslk < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  // keep the watch, check for propagation
  int watchprops = 0;
  stats.NPROPCHECKS -= watchIdx;
  for (; watchIdx < length && aux::abs(terms[watchIdx].c) > wslk; ++watchIdx) {
    const Lit l = terms[watchIdx].l;
    if (isUnknown(position, l)) {
      stats.NPROPCLAUSE += (*degr == 1);
      stats.NPROPCARD += (*degr != 1 && lrgstCf == 1);
      ++watchprops;
      assert(isCorrectlyPropagating(solver, watchIdx));
      solver.propagate(l, cr);
    }  // NOTE: second innermost loop
  }
  stats.NPROPCHECKS += watchIdx;
  stats.NPROPWATCH += watchprops;
  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void WatchedSafe<CF, DG>::undoFalsified(int i) {
  assert(i >= INF);
  assert(terms[i - INF].c < 0);
  *watchslack -= terms[i - INF].c;
}

template <typename CF, typename DG>
int WatchedSafe<CF, DG>::resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const {
  return confl->resolveWith(terms, size, *degr, id, getOrigin(), l, solver.getLevel(), solver.getPos(), actSet);
}
template <typename CF, typename DG>
int WatchedSafe<CF, DG>::subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const {
  return confl->subsumeWith(terms, size, *degr, id, l, solver.getLevel(), solver.getPos(), saturatedLits);
}

template <typename CF, typename DG>
CePtr<CF, DG> WatchedSafe<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<CF, DG> result = cePools.take<CF, DG>();
  result->addRhs(*degr);
  for (size_t i = 0; i < size; ++i) {
    result->addLhs(aux::abs(terms[i].c), terms[i].l);
  }
  result->orig = getOrigin();
  result->resetBuffer(id);
  return result;
}

template <typename CF, typename DG>
CeSuper WatchedSafe<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::isSatisfiedAtRoot(const IntMap<int>& level) const {
  DG eval = -*degr;
  for (int i = 0; i < (int)size && eval < 0; ++i) {
    if (isUnit(level, terms[i].l)) eval += aux::abs(terms[i].c);
  }
  return eval >= 0;
}

template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                                          IntSetPool& isp) const {
  bool isEquality = getOrigin() == Origin::EQUALITY;
  for (int i = 0; i < (int)size; ++i) {
    Lit l = terms[i].l;
    if (isUnit(level, l) || isUnit(level, -l) || (!isEquality && !equalities.isCanonical(l))) return true;
  }
  if (!isEquality) {
    IntSet& hasImplieds = isp.take();
    for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
      Lit l = terms[i].l;
      if (implications.hasImplieds(l)) hasImplieds.add(-l);
    }
    if (!hasImplieds.isEmpty()) {
      for (int i = 0; i < (int)getUnsaturatedIdx(); ++i) {
        if (hasImplieds.has(terms[i].l)) {
          isp.release(hasImplieds);
          return true;
        }
      }
    }
    isp.release(hasImplieds);
  }
  return false;
}

// TODO: keep below test methods?

bool Constr::isCorrectlyConflicting(const Solver& solver) const {
  return true;  // comment to run check
  bigint slack = -degree();
  for (int i = 0; i < (int)size; ++i) {
    slack += isFalse(solver.getLevel(), lit(i)) ? 0 : coef(i);
  }
  return slack < 0;
}

bool Constr::isCorrectlyPropagating(const Solver& solver, int idx) const {
  return true;  // comment to run check
  assert(isUnknown(solver.getPos(), lit(idx)));
  bigint slack = -degree();
  for (int i = 0; i < (int)size; ++i) {
    slack += isFalse(solver.getLevel(), lit(i)) ? 0 : coef(i);
  }
  return slack < coef(idx);
}

void Constr::print(const Solver& solver) const {
  for (size_t i = 0; i < size; ++i) {
    int pos = solver.getPos()[toVar(lit(i))];
    std::cout << coef(i) << "x" << lit(i)
              << (pos < solver.qhead ? (isTrue(solver.getLevel(), lit(i)) ? "t" : "f") : "u") << (pos == INF ? -1 : pos)
              << " ";
  }
  std::cout << ">= " << degree() << std::endl;
}

template <typename CF, typename DG>
bool Counting<CF, DG>::hasCorrectSlack(const Solver& solver) {
  return true;  // comment to run check
  DG slk = -degr;
  for (int i = 0; i < (int)size; ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slk += data[i].c;
    }
  }
  return (slk == slack);
}

template <typename CF, typename DG>
bool Watched<CF, DG>::hasCorrectSlack(const Solver& solver) {
  return true;  // comment to run check
  DG slk = -degr;
  for (int i = 0; i < (int)size; ++i) {
    if (data[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))))
      slk += aux::abs(data[i].c);
  }
  return (slk == watchslack);
}

template <typename CF, typename DG>
bool CountingSafe<CF, DG>::hasCorrectSlack(const Solver& solver) {
  return true;  // comment to run check
  DG slk = -*degr;
  for (int i = 0; i < (int)size; ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slk += terms[i].c;
    }
  }
  return (slk == *slack);
}

template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::hasCorrectSlack(const Solver& solver) {
  return true;  // comment to run check
  DG slk = -*degr;
  for (int i = 0; i < (int)size; ++i) {
    if (terms[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))))
      slk += aux::abs(terms[i].c);
  }
  return (slk == *watchslack);
}

template <typename CF, typename DG>
bool Watched<CF, DG>::hasCorrectWatches(const Solver& solver) {
  return true;  // comment to run check
  if (watchslack >= aux::abs(data[0].c)) return true;
  for (int i = 0; i < (int)watchIdx; ++i) assert(isKnown(solver.getPos(), lit(i)));
  for (int i = 0; i < (int)size; ++i) {
    if (!(data[i].c < 0 || isFalse(solver.getLevel(), data[i].l))) {
      std::cout << i << " " << data[i].c << " " << isFalse(solver.getLevel(), data[i].l) << std::endl;
      print(solver);
    }
    assert(data[i].c < 0 || isFalse(solver.getLevel(), data[i].l));
  }
  return true;
}

template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::hasCorrectWatches(const Solver& solver) {
  return true;  // comment to run check
  if (*watchslack >= aux::abs(terms[0].c)) return true;
  for (int i = 0; i < (int)watchIdx; ++i) assert(isKnown(solver.getPos(), lit(i)));
  for (int i = 0; i < (int)size; ++i) {
    if (!(terms[i].c < 0 || isFalse(solver.getLevel(), terms[i].l))) {
      std::cout << i << " " << terms[i].c << " " << isFalse(solver.getLevel(), terms[i].l) << std::endl;
      print(solver);
    }
    assert(terms[i].c < 0 || isFalse(solver.getLevel(), terms[i].l));
  }
  return true;
}

template struct Counting<int, long long>;

template struct Watched<int, long long>;

template struct CountingSafe<long long, int128>;
template struct CountingSafe<int128, int128>;
template struct CountingSafe<int128, int256>;
template struct CountingSafe<bigint, bigint>;

template struct WatchedSafe<long long, int128>;
template struct WatchedSafe<int128, int128>;
template struct WatchedSafe<int128, int256>;
template struct WatchedSafe<bigint, bigint>;

}  // namespace xct
