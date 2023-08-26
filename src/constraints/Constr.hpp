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

#include "../typedefs.hpp"
#include "ConstrExp.hpp"

namespace xct {

enum class WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };
const unsigned int LBDBITS = 24;
const unsigned int SAFELBD = (((unsigned int)1) << LBDBITS) - 1;
// TODO: use SAFELBD to keep fresh constraints active for one round
const unsigned int MAXLBD = SAFELBD - 1;

class Solver;
class Equalities;
struct Stats;

struct Constr {  // internal solver constraint optimized for fast propagation
  virtual size_t getMemSize() const = 0;

  const ID id;
  // NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
  const float strength;
  const unsigned int size;
  struct {
    unsigned markedfordel : 1;
    unsigned locked : 1;
    unsigned seen : 1;  // utility bit to avoid hash maps
    const unsigned origin : 5;
    unsigned lbd : LBDBITS;
  } header;

  Constr(ID i, Origin o, bool lkd, unsigned int lngth, float strngth);
  virtual ~Constr() {}
  virtual void cleanup() = 0;  // poor man's destructor

  void setLocked(bool lkd) { header.locked = lkd; }
  bool isLocked() const { return header.locked; }
  Origin getOrigin() const { return (Origin)header.origin; }
  void decreaseLBD(unsigned int lbd) { header.lbd = std::min(header.lbd, lbd); }
  void decayLBD(unsigned int decay) { header.lbd = std::min({header.lbd + decay, MAXLBD}); }
  unsigned int lbd() const { return header.lbd; }
  bool isMarkedForDelete() const { return header.markedfordel; }
  bool isSeen() const { return header.seen; }
  void setSeen(bool s) { header.seen = s; }
  void fixEncountered(Stats& stats) const;

  // TODO: remove direct uses of these bigint methods, convert to ConstrExp instead
  // NOTE: useful for debugging though!
  virtual bigint degree() const = 0;
  virtual bigint coef(unsigned int i) const = 0;
  bigint largestCoef() const { return coef(0); };
  virtual Lit lit(unsigned int i) const = 0;
  virtual unsigned int getUnsaturatedIdx() const = 0;
  virtual bool isClauseOrCard() const = 0;
  virtual bool isAtMostOne() const = 0;

  virtual void initializeWatches(CRef cr, Solver& solver) = 0;
  virtual WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& slvr, Stats& stats) = 0;
  virtual void undoFalsified(int i) = 0;
  virtual int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const = 0;
  virtual int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const = 0;

  virtual CeSuper toExpanded(ConstrExpPools& cePools) const = 0;
  virtual bool isSatisfiedAtRoot(const IntMap<int>& level) const = 0;
  virtual bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                               IntSetPool& isp) const = 0;

  void print(const Solver& solver) const;

  bool isCorrectlyConflicting(const Solver& solver) const;
  bool isCorrectlyPropagating(const Solver& solver, int idx) const;
};
std::ostream& operator<<(std::ostream& o, const Constr& c);

struct Clause final : public Constr {
  Lit data[];

  static size_t getMemSize(unsigned int length) { return (sizeof(Clause) + sizeof(Lit) * length) / sizeof(uint32_t); }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return 1; }
  bigint coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }
  unsigned int getUnsaturatedIdx() const { return size; }
  bool isClauseOrCard() const { return true; }
  bool isAtMostOne() const { return size == 2; }

  template <typename SMALL, typename LARGE>
  Clause(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(), 1 / (float)constraint->nVars()) {
    assert(_id > ID_Trivial);
    assert(constraint->nVars() < INF);
    assert(constraint->getDegree() == 1);

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      data[i] = constraint->getLit(v);
    }
  }

  void cleanup() {}

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, Stats& stats);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;
};

struct Cardinality final : public Constr {
  unsigned int watchIdx;
  unsigned int degr;
  long long ntrailpops;
  Lit data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Cardinality) + sizeof(Lit) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return degr; }
  bigint coef([[maybe_unused]] unsigned int i) const { return 1; }
  Lit lit(unsigned int i) const { return data[i]; }
  unsigned int getUnsaturatedIdx() const { return 0; }
  bool isClauseOrCard() const { return true; }
  bool isAtMostOne() const { return degr == size - 1; }

  template <typename SMALL, typename LARGE>
  Cardinality(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(),
               static_cast<float>(constraint->getDegree()) / constraint->nVars()),
        watchIdx(0),
        degr(static_cast<unsigned int>(constraint->getDegree())),
        ntrailpops(-1) {
    assert(degr > 1);  // otherwise should be a clause
    assert(_id > ID_Trivial);
    assert(constraint->nVars() < INF);
    assert(aux::abs(constraint->coefs[constraint->getVars()[0]]) == 1);
    assert(constraint->getDegree() <= (LARGE)constraint->nVars());

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      data[i] = constraint->getLit(v);
    }
  }

  void cleanup() {}

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, Stats& stats);
  void undoFalsified([[maybe_unused]] int i) { assert(false); }
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;
};

template <typename CF, typename DG>
struct Counting final : public Constr {
  unsigned int unsaturatedIdx;
  unsigned int watchIdx;
  long long ntrailpops;
  const DG degr;
  DG slack;
  Term<CF> data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Counting<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return degr; }
  bigint coef(unsigned int i) const { return data[i].c; }
  Lit lit(unsigned int i) const { return data[i].l; }
  unsigned int getUnsaturatedIdx() const { return unsaturatedIdx; }
  bool isClauseOrCard() const {
    assert(largestCoef() > 1);
    return false;
  }
  bool isAtMostOne() const {
    assert(largestCoef() > 1);
    return false;
  }

  template <typename SMALL, typename LARGE>
  Counting(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(), constraint->getStrength()),
        unsaturatedIdx(0),
        watchIdx(0),
        ntrailpops(-1),
        degr(static_cast<DG>(constraint->getDegree())),
        slack(0) {
    assert(_id > ID_Trivial);
    assert(fitsIn<DG>(constraint->getDegree()));
    assert(fitsIn<CF>(constraint->getLargestCoef()));

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      data[i] = {static_cast<CF>(aux::abs(constraint->coefs[v])), constraint->getLit(v)};
      unsaturatedIdx += data[i].c >= degr;
      assert(data[i].c <= degr);
    }
  }

  void cleanup() {}

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver, Stats& stats);
  void undoFalsified(int i);
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CePtr<CF, DG> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;

  bool hasCorrectSlack(const Solver& solver);
};

template <typename CF, typename DG>
struct Watched final : public Constr {
  unsigned int unsaturatedIdx;
  unsigned int watchIdx;
  long long ntrailpops;
  const DG degr;
  DG watchslack;
  Term<CF> data[];

  static size_t getMemSize(unsigned int length) {
    return (sizeof(Watched<CF, DG>) + sizeof(Term<CF>) * length) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return degr; }
  bigint coef(unsigned int i) const { return aux::abs(data[i].c); }
  Lit lit(unsigned int i) const { return data[i].l; }
  unsigned int getUnsaturatedIdx() const { return unsaturatedIdx; }
  bool isClauseOrCard() const {
    assert(largestCoef() > 1);
    return false;
  }
  bool isAtMostOne() const {
    assert(largestCoef() > 1);
    return false;
  }

  template <typename SMALL, typename LARGE>
  Watched(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(), constraint->getStrength()),
        unsaturatedIdx(0),
        watchIdx(0),
        ntrailpops(-1),
        degr(static_cast<DG>(constraint->getDegree())),
        watchslack(0) {
    assert(_id > ID_Trivial);
    assert(fitsIn<DG>(constraint->getDegree()));
    assert(fitsIn<CF>(constraint->getLargestCoef()));

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      data[i] = {static_cast<CF>(aux::abs(constraint->coefs[v])), constraint->getLit(v)};
      unsaturatedIdx += data[i].c >= degr;
      assert(data[i].c <= degr);
    }
  }

  void cleanup() {}

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver, Stats& stats);
  void undoFalsified(int i);
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CePtr<CF, DG> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;

  bool hasCorrectSlack(const Solver& solver);
  bool hasCorrectWatches(const Solver& solver);
};

template <typename CF, typename DG>
struct CountingSafe final : public Constr {
  unsigned int unsaturatedIdx;
  unsigned int watchIdx;
  long long ntrailpops;
  DG* degr;
  DG* slack;
  Term<CF>* terms;  // array

  static size_t getMemSize([[maybe_unused]] unsigned int length) {
    return sizeof(CountingSafe<CF, DG>) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return bigint(*degr); }
  bigint coef(unsigned int i) const { return bigint(terms[i].c); }
  Lit lit(unsigned int i) const { return terms[i].l; }
  unsigned int getUnsaturatedIdx() const { return unsaturatedIdx; }
  bool isClauseOrCard() const {
    assert(largestCoef() > 1);
    return false;
  }
  bool isAtMostOne() const {
    assert(largestCoef() > 1);
    return false;
  }

  template <typename SMALL, typename LARGE>
  CountingSafe(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(), constraint->getStrength()),
        unsaturatedIdx(0),
        watchIdx(0),
        ntrailpops(-1),
        degr(new DG(static_cast<DG>(constraint->getDegree()))),
        slack(new DG(0)),
        terms(new Term<CF>[constraint->nVars()]) {
    assert(_id > ID_Trivial);
    assert(fitsIn<DG>(constraint->getDegree()));
    assert(fitsIn<CF>(constraint->getLargestCoef()));

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      terms[i] = {static_cast<CF>(aux::abs(constraint->coefs[v])), constraint->getLit(v)};
      unsaturatedIdx += terms[i].c >= *degr;
      assert(terms[i].c <= *degr);
    }
  }

  void cleanup() {
    delete degr;
    delete slack;
    delete[] terms;
  }

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, Stats& stats);
  void undoFalsified(int i);
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CePtr<CF, DG> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;

  bool hasCorrectSlack(const Solver& solver);
};

template <typename CF, typename DG>
struct WatchedSafe final : public Constr {
  unsigned int unsaturatedIdx;
  unsigned int watchIdx;
  long long ntrailpops;
  DG* degr;
  DG* watchslack;
  Term<CF>* terms;  // array

  static size_t getMemSize([[maybe_unused]] unsigned int length) {
    return sizeof(WatchedSafe<CF, DG>) / sizeof(uint32_t);
  }
  size_t getMemSize() const { return getMemSize(size); }

  bigint degree() const { return bigint(*degr); }
  bigint coef(unsigned int i) const { return bigint(aux::abs(terms[i].c)); }
  Lit lit(unsigned int i) const { return terms[i].l; }
  unsigned int getUnsaturatedIdx() const { return unsaturatedIdx; }
  bool isClauseOrCard() const {
    assert(largestCoef() > 1);
    return false;
  }
  bool isAtMostOne() const {
    assert(largestCoef() > 1);
    return false;
  }

  template <typename SMALL, typename LARGE>
  WatchedSafe(const ConstrExp<SMALL, LARGE>* constraint, bool locked, ID _id)
      : Constr(_id, constraint->orig, locked, constraint->nVars(), constraint->getStrength()),
        unsaturatedIdx(0),
        watchIdx(0),
        ntrailpops(-1),
        degr(new DG(static_cast<DG>(constraint->getDegree()))),
        watchslack(new DG(0)),
        terms(new Term<CF>[constraint->nVars()]) {
    assert(_id > ID_Trivial);
    assert(fitsIn<DG>(constraint->getDegree()));
    assert(fitsIn<CF>(constraint->getLargestCoef()));

    for (unsigned int i = 0; i < size; ++i) {
      Var v = constraint->getVars()[i];
      assert(constraint->getLit(v) != 0);
      terms[i] = {static_cast<CF>(aux::abs(constraint->coefs[v])), constraint->getLit(v)};
      unsaturatedIdx += terms[i].c >= *degr;
      assert(terms[i].c <= *degr);
    }
  }

  void cleanup() {
    delete degr;
    delete watchslack;
    delete[] terms;
  }

  void initializeWatches(CRef cr, Solver& solver);
  WatchStatus checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver, Stats& stats);
  void undoFalsified(int i);
  int resolveWith(CeSuper confl, Lit l, Solver& solver, IntSet& actSet) const;
  int subsumeWith(CeSuper confl, Lit l, Solver& solver, IntSet& saturatedLits) const;

  CePtr<CF, DG> expandTo(ConstrExpPools& cePools) const;
  CeSuper toExpanded(ConstrExpPools& cePools) const;
  bool isSatisfiedAtRoot(const IntMap<int>& level) const;
  bool canBeSimplified(const IntMap<int>& level, Equalities& equalities, Implications& implications,
                       IntSetPool& isp) const;

  bool hasCorrectSlack(const Solver& solver);
  bool hasCorrectWatches(const Solver& solver);
};

}  // namespace xct
