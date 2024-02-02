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

#include "ConstrExp.hpp"
#include <algorithm>
#include <functional>
#include "../Solver.hpp"
#include "../auxiliary.hpp"
#include "../datastructures/Heuristic.hpp"
#include "../datastructures/IntSet.hpp"
#include "../propagation/Equalities.hpp"
#include "../propagation/Implications.hpp"
#include "Constr.hpp"

namespace xct {

ConstrExpSuper::ConstrExpSuper(Global& g) : global(g), orig(Origin::UNKNOWN) {}

void ConstrExpSuper::resetBuffer(ID proofID) {
  if (!global.logger.isActive()) return;
  assert(proofID != ID_Undef);
  proofBuffer.clear();
  proofBuffer.str(std::string());
  proofBuffer << proofID << " ";
}

void ConstrExpSuper::resetBuffer(const std::string& line) {
  if (!global.logger.isActive()) return;
  proofBuffer.clear();
  proofBuffer.str(std::string());
  proofBuffer << line;
}

std::ostream& operator<<(std::ostream& o, const ConstrExpSuper& ce) {
  ce.toStreamAsOPB(o);
  return o;
}
std::ostream& operator<<(std::ostream& o, const CeSuper& ce) { return o << *ce; }

template <typename SMALL, typename LARGE>
ConstrExp<SMALL, LARGE>::ConstrExp(Global& g) : ConstrExpSuper(g) {
  reset(false);
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::copyTo(const Ce32& ce) const {
  copyTo_(ce);
}
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::copyTo(const Ce64& ce) const {
  copyTo_(ce);
}
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::copyTo(const Ce96& ce) const {
  copyTo_(ce);
}
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::copyTo(const Ce128& ce) const {
  copyTo_(ce);
}
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::copyTo(const CeArb& ce) const {
  copyTo_(ce);
}

template <typename SMALL, typename LARGE>
CeSuper ConstrExp<SMALL, LARGE>::clone(ConstrExpPools& cePools) const {
  LARGE maxVal = getCutoffVal();
  if (maxVal <= static_cast<LARGE>(limitAbs<int, long long>())) {
    Ce32 result = cePools.take32();
    copyTo(result);
    return result;
  } else if (maxVal <= static_cast<LARGE>(limitAbs<long long, int128>())) {
    Ce64 result = cePools.take64();
    copyTo(result);
    return result;
  } else if (maxVal <= static_cast<LARGE>(limitAbs<int128, int128>())) {
    Ce96 result = cePools.take96();
    copyTo(result);
    return result;
  } else if (maxVal <= static_cast<LARGE>(limitAbs<int128, int256>())) {
    Ce128 result = cePools.take128();
    copyTo(result);
    return result;
  } else {
    CeArb result = cePools.takeArb();
    copyTo(result);
    return result;
  }
}

template <typename SMALL, typename LARGE>
CRef ConstrExp<SMALL, LARGE>::toConstr(ConstraintAllocator& ca, bool locked, ID id) const {
  // assert(testConstraint());
  assert(isSortedInDecreasingCoefOrder());
  assert(isSaturated());
  assert(hasNoZeroes());
  assert(!vars.empty());
  assert(!isTautology());
  assert(!isInconsistency());

  CRef result = CRef{ca.at};
  SMALL maxCoef = aux::abs(coefs[vars[0]]);
  if (isClause()) {
    new (ca.alloc<Clause>(vars.size())) Clause(this, locked, id);
  } else if (maxCoef == 1) {
    new (ca.alloc<Cardinality>(vars.size())) Cardinality(this, locked, id);
  } else {
    double strngth = getStrength();
    bool useCounting = strngth > global.options.propWatched.get();
    global.stats.NCOUNTING += useCounting;
    global.stats.NWATCHED += !useCounting;
    if (maxCoef <= static_cast<LARGE>(limitAbs<int, long long>())) {
      global.stats.NSMALL += 1;
      if (useCounting) {
        new (ca.alloc<Counting32>(vars.size())) Counting32(this, locked, id, strngth);
      } else {
        new (ca.alloc<Watched32>(vars.size())) Watched32(this, locked, id, strngth);
      }
    } else if (maxCoef <= static_cast<LARGE>(limitAbs<long long, int128>())) {
      global.stats.NLARGE += 1;
      if (useCounting) {
        new (ca.alloc<Counting64>(vars.size())) Counting64(this, locked, id, strngth);
      } else {
        new (ca.alloc<Watched64>(vars.size())) Watched64(this, locked, id, strngth);
      }
    } else if (maxCoef <= static_cast<LARGE>(limitAbs<int128, int128>())) {
      global.stats.NLARGE += 1;
      if (useCounting) {
        new (ca.alloc<Counting96>(vars.size())) Counting96(this, locked, id, strngth);
      } else {
        new (ca.alloc<Watched96>(vars.size())) Watched96(this, locked, id, strngth);
      }
    } else if (maxCoef <= static_cast<LARGE>(limitAbs<int128, int256>())) {
      global.stats.NLARGE += 1;
      if (useCounting) {
        new (ca.alloc<Counting128>(vars.size())) Counting128(this, locked, id, strngth);
      } else {
        new (ca.alloc<Watched128>(vars.size())) Watched128(this, locked, id, strngth);
      }
    } else {
      global.stats.NARB += 1;
      if (useCounting) {
        new (ca.alloc<CountingArb>(vars.size())) CountingArb(this, locked, id, strngth);
      } else {
        new (ca.alloc<WatchedArb>(vars.size())) WatchedArb(this, locked, id, strngth);
      }
    }
  }
  return result;
}

template <typename SMALL, typename LARGE>
std::unique_ptr<ConstrSimpleSuper> ConstrExp<SMALL, LARGE>::toSimple() const {
  LARGE maxVal = getCutoffVal();
  if (maxVal <= static_cast<LARGE>(limitAbs<int, long long>())) {
    return toSimple_<int, long long>();
  } else if (maxVal <= static_cast<LARGE>(limitAbs<long long, int128>())) {
    return toSimple_<long long, int128>();
  } else if (maxVal <= static_cast<LARGE>(limitAbs<int128, int128>())) {
    return toSimple_<int128, int128>();
  } else if (maxVal <= static_cast<LARGE>(limitAbs<int128, int256>())) {
    return toSimple_<int128, int256>();
  } else {
    return toSimple_<bigint, bigint>();
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::add(Var v, SMALL c, bool removeZeroes) {
  if (c == 0) return;
  SMALL& cf = coefs[v];
  if (!used(v)) {
    assert(cf == 0);
    cf = c;
    index[v] = vars.size();
    vars.push_back(v);
  } else {
    if ((cf < 0) != (c < 0)) degree -= std::min(aux::abs(cf), aux::abs(c));
    cf += c;
    if (removeZeroes && cf == 0) remove(v);
  }
  assert(!(removeZeroes && cf == 0 && used(v)));
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::remove(Var v) {
  assert(used(v));
  coefs[v] = 0;
  Var replace = vars.back();
  assert(vars[index[v]] == v);
  vars[index[v]] = replace;
  index[replace] = index[v];
  index[v] = -1;
  vars.pop_back();
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::increasesSlack(const IntMap<int>& level, Var v) const {
  return isTrue(level, v) || (!isFalse(level, v) && coefs[v] > 0);
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::calcDegree() const {
  LARGE res = rhs;
  for (Var v : vars) res -= std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
  return res;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::calcRhs() const {
  LARGE res = degree;
  for (Var v : vars) res += std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
  return res;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::testConstraint() const {
  assert(degree == calcDegree());
  assert(rhs == calcRhs());
  assert(coefs.size() == index.size());
  unordered_set<Var> usedvars;
  usedvars.insert(vars.cbegin(), vars.cend());
  for (Var v = 1; v < (int)coefs.size(); ++v) {
    assert(used(v) || coefs[v] == 0);
    assert(usedvars.count(v) == used(v));
    assert(index[v] == -1 || vars[index[v]] == v);
  }
  return true;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::resize(size_t s) {
  if (s > coefs.size()) {
    coefs.resize(s, 0);
    index.resize(s, -1);
  }
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isReset() const {
  return vars.empty() && rhs == 0 && degree == 0;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::reset(bool partial) {
  for (Var v : vars) {
    coefs[v] = 0;
    index[v] = -1;
  }
  vars.clear();
  rhs = 0;
  degree = 0;
  if (!partial) {
    orig = Origin::UNKNOWN;
    resetBuffer(ID_Trivial);
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::addRhs(const LARGE& r) {
  rhs += r;
  degree += r;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getRhs() const {
  return rhs;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getDegree() const {
  return degree;
}

template <typename SMALL, typename LARGE>
double ConstrExp<SMALL, LARGE>::getStrength() const {
  LARGE coefsum = 0;
  for (Var v : vars) {
    coefsum += aux::abs(coefs[v]);
  }
  return aux::divToDouble(degree, coefsum);
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getCoef(Lit l) const {
  assert((unsigned int)toVar(l) < coefs.size());
  return l < 0 ? -coefs[-l] : coefs[l];
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::absCoef(Var v) const {  // TODO: refactor other usages
  assert(0 <= v);
  assert(v < (Var)coefs.size());
  return aux::abs(coefs[v]);
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::nthCoef(int i) const {  // TODO: refactor other usages
  assert(0 <= i);
  assert(i < (int)vars.size());
  return absCoef(vars[i]);
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getLargestCoef(const std::vector<Var>& vs) const {
  SMALL result = 0;
  for (Var v : vs) result = std::max(result, aux::abs(coefs[v]));
  return result;
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getLargestCoef() const {
  return getLargestCoef(vars);
}

template <typename SMALL, typename LARGE>
SMALL ConstrExp<SMALL, LARGE>::getSmallestCoef() const {
  assert(!vars.empty());
  SMALL result = aux::abs(coefs[vars[0]]);
  for (Var v : vars) result = std::min(result, aux::abs(coefs[v]));
  return result;
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getCutoffVal() const {
  return std::max<LARGE>(getLargestCoef(), std::max(degree, aux::abs(rhs)) / INF);
}

template <typename SMALL, typename LARGE>
Lit ConstrExp<SMALL, LARGE>::getLit(Var v) const {  // NOTE: answer of 0 means coef 0
  assert(v >= 0);
  assert(v < (Var)coefs.size());
  return (coefs[v] == 0) ? 0 : (coefs[v] < 0 ? -v : v);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasLit(Lit l) const {
  Var v = toVar(l);
  assert(v < (Var)coefs.size());
  return coefs[v] != 0 && (coefs[v] < 0) == (l < 0);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasVar(Var v) const {
  assert(v > 0);
  return coefs[v] != 0;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::saturatedLit(Lit l) const {
  Var v = toVar(l);
  return (coefs[v] < 0) == (l < 0) && aux::abs(coefs[v]) >= degree;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::saturatedVar(Var v) const {
  return aux::abs(coefs[v]) >= degree;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::falsified(const IntMap<int>& level, Var v) const {
  assert(v > 0);
  assert((getLit(v) != 0 && !isFalse(level, getLit(v))) == (coefs[v] > 0 && !isFalse(level, v)) ||
         (coefs[v] < 0 && !isTrue(level, v)));
  return (coefs[v] > 0 && isFalse(level, v)) || (coefs[v] < 0 && isTrue(level, v));
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getSlack(const IntMap<int>& level) const {
  LARGE slack = -rhs;
  for (Var v : vars)
    if (increasesSlack(level, v)) slack += coefs[v];
  return slack;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasNegativeSlack(const IntMap<int>& level) const {
  return getSlack(level) < 0;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isTautology() const {
  return getDegree() <= 0;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isInconsistency() const {
  return getDegree() > absCoeffSum();
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSatisfied(const std::vector<Lit>& assignment) const {
  LARGE eval = -degree;
  for (Var v : vars) {
    if (assignment[v] == getLit(v)) eval += aux::abs(coefs[v]);
  }
  return eval >= 0;
}

template <typename SMALL, typename LARGE>
unsigned int ConstrExp<SMALL, LARGE>::getLBD(const IntMap<int>& level) const {
  // calculate delete-lbd-e according to "On Dedicated CDCL Strategies for PB Solvers" - Le Berre & Wallon - 2021
  assert(isSortedInDecreasingCoefOrder());
  LARGE weakenedDeg = degree;
  for (Var v : vars) {  // weaken all non-falsifieds
    if (!isFalse(level, getLit(v))) {
      weakenedDeg -= aux::abs(coefs[v]);
      if (weakenedDeg <= 0) break;
    }
  }
  int i = vars.size() - 1;
  if (weakenedDeg > 0) {
    for (; i >= 0; --i) {  // weaken all smallest falsifieds
      Var v = vars[i];
      Lit l = getLit(v);
      if (isFalse(level, l)) {
        weakenedDeg -= aux::abs(coefs[v]);
        if (weakenedDeg <= 0) break;
      }
    }
  }
  assert(i >= 0);  // constraint is asserting or conflicting
  IntSet& lbdSet = global.isPool.take();
  for (; i >= 0; --i) {  // gather all levels
    lbdSet.add(level[-getLit(vars[i])] % INF);
  }
  lbdSet.remove(0);  // unit literals and non-falsifieds should not be counted
  unsigned int lbd = lbdSet.size();
  global.isPool.release(lbdSet);
  return lbd;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::addLhs(const SMALL& cf, Lit l) {  // add c*(l>=0) if c>0 and -c*(-l>=0) if c<0
  if (cf == 0) return;
  assert(l != 0);
  SMALL c = cf;
  if (c < 0) degree -= c;
  Var v = l;
  if (l < 0) {
    rhs -= c;
    c = -c;
    v = -l;
  }
  assert(v < (Var)coefs.size());
  add(v, c);
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weaken(const SMALL& m, Var v) {  // add m*(v>=0) if m>0 and -m*(-v>=-1) if m<0
  assert(v > 0);
  assert(v < (Var)coefs.size());
  assert(coefs[v] != 0);
  if (global.logger.isActive() && m != 0) {
    Logger::proofWeaken(proofBuffer, v, m);
  }

  const bool tmp = m < 0;
  SMALL& c = coefs[v];
  if ((c < 0) != tmp) {
    degree -= std::min(aux::abs(c), aux::abs(m));
  }
  if (tmp) {
    rhs += m;
  }
  c += m;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weaken(Var v) {  // fully weaken v
  weaken(-coefs[v], v);
}

void ConstrExpSuper::weakenLast() {
  if (vars.empty()) return;
  weaken(vars.back());
  popLast();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weaken(const aux::predicate<Lit>& toWeaken) {
  for (Var v : vars) {
    if (coefs[v] != 0 && toWeaken(getLit(v))) {
      weaken(v);
    }
  }
}

void ConstrExpSuper::popLast() {
  assert(!vars.empty());
  assert(!hasVar(vars.back()));
  index[vars.back()] = -1;
  vars.pop_back();
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::removeUnitsAndZeroes(const IntMap<int>& level, const std::vector<int>& pos) {
  if (global.logger.isActive()) {
    for (Var v : vars) {
      Lit l = getLit(v);
      if (l != 0) {
        if (isUnit(level, l)) {
          Logger::proofWeaken(proofBuffer, l, -getCoef(l));
        } else if (isUnit(level, -l)) {
          Logger::proofWeakenFalseUnit(proofBuffer, global.logger.getUnitID(pos[toVar(l)]), -getCoef(l));
        }
      }
    }
  }
  int j = 0;
  for (int i = 0; i < (int)vars.size(); ++i) {
    Var v = vars[i];
    if (coefs[v] == 0)
      index[v] = -1;
    else if (isUnit(level, v)) {
      rhs -= coefs[v];
      if (coefs[v] > 0) degree -= coefs[v];
      index[v] = -1;
      coefs[v] = 0;
    } else if (isUnit(level, -v)) {
      if (coefs[v] < 0) degree += coefs[v];
      index[v] = -1;
      coefs[v] = 0;
    } else {
      index[v] = j;
      vars[j++] = v;
    }
  }
  vars.resize(j);
}

bool ConstrExpSuper::hasNoUnits(const IntMap<int>& level) const {
  return std::all_of(vars.cbegin(), vars.cend(), [&](Var v) { return !isUnit(level, v) && !isUnit(level, -v); });
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::removeZeroes() {
  int j = 0;
  for (int i = 0; i < (int)vars.size(); ++i) {
    Var v = vars[i];
    if (coefs[v] == 0) {
      index[v] = -1;
    } else {
      index[v] = j;
      vars[j++] = v;
    }
  }
  vars.resize(j);
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::removeEqualities(Equalities& equalities, bool _saturate) {
  if (_saturate) saturate(true, false);
  int oldsize = vars.size();  // newly added literals are their own canonical representative
  for (int i = 0; i < oldsize && degree > 0; ++i) {
    Var v = vars[i];
    Lit l = getLit(v);
    if (l == 0) continue;
    if (const Repr& repr = equalities.getRepr(l); repr.l != l) {  // literal is not its own canonical representative
      SMALL mult = _saturate ? static_cast<SMALL>(std::min<LARGE>(degree, aux::abs(coefs[v]))) : aux::abs(coefs[v]);
      addLhs(mult, repr.l);
      Var reprv = toVar(repr.l);
      if (stillFits<SMALL>(coefs[reprv]) ||
          (_saturate && aux::abs(coefs[reprv]) >= degree && stillFits<SMALL>(static_cast<SMALL>(degree)))) {
        addLhs(mult, -l);
        addRhs(mult);
        coefs[v] = 0;
        if (global.logger.isActive())
          Logger::proofMult(proofBuffer << repr.id << " ", mult) << (_saturate ? "+ s " : "+ ");
        if (_saturate) saturate(reprv);
      } else {
        addLhs(-mult, repr.l);  // revert change
      }
    }
  }
  if (_saturate) saturate(true, false);
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::selfSubsumeImplications(const Implications& implications) {
  saturate(true, false);  // needed to get the proof to agree
  IntSet& saturateds = global.isPool.take();
  getSaturatedLits(saturateds);
  for (Var v : vars) {
    if (coefs[v] == 0) continue;
    Lit l = getLit(v);
    for (Lit ll : implications.getImplieds(l)) {
      if (!saturateds.has(ll)) continue;
      ++global.stats.NSUBSUMESTEPS;
      SMALL cf = aux::abs(coefs[v]);
      if (global.logger.isActive()) Logger::proofMult(proofBuffer << global.logger.logRUP(-l, ll) << " ", cf) << "+ s ";
      addRhs(cf);
      addLhs(cf, -l);
      assert(coefs[v] == 0);
      saturateds.remove(l);
      assert(!saturateds.has(-l));
      break;
    }
  }
  global.isPool.release(saturateds);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::hasNoZeroes() const {
  return std::all_of(vars.cbegin(), vars.cend(), [&](Var v) { return coefs[v] != 0; });
}

// @post: preserves order of vars
// NOTE: other variables should already be saturated, otherwise proof logging will break
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturate(const std::vector<Var>& vs, bool check, bool sorted) {
  global.stats.NSATURATESTEPS += vs.size();
  assert(check || !sorted);
  if (vars.empty() || (sorted && aux::abs(coefs[vars[0]]) <= degree) ||
      (!sorted && check && getLargestCoef() <= degree)) {
    return;
  }
  assert(getLargestCoef() > degree);
  if (global.logger.isActive()) proofBuffer << "s ";  // log saturation only if it modifies the constraint
  SMALL smallDeg = static_cast<SMALL>(degree);        // safe cast because of above assert
  if (smallDeg <= 0) {
    reset(false);
    return;
  }
  for (Var v : vs) {
    if (coefs[v] < -smallDeg) {
      rhs -= coefs[v] + smallDeg;
      coefs[v] = -smallDeg;
    } else if (coefs[v] > smallDeg) {
      coefs[v] = smallDeg;
    } else if (sorted) {
      break;
    }
  }
  assert(isSaturated());
}

// NOTE: use judiciously, be careful of adding correct saturation lines in the proof
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturate(Var v) {
  assert(degree >= 0);
  if (aux::abs(coefs[v]) <= degree) return;
  SMALL smallDeg = static_cast<SMALL>(degree);
  if (coefs[v] < -smallDeg) {
    rhs -= coefs[v] + smallDeg;
    coefs[v] = -smallDeg;
  } else {
    assert(coefs[v] > smallDeg);
    coefs[v] = smallDeg;
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturate(bool check, bool sorted) {
  saturate(vars, check, sorted);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSaturated() const {
  return getLargestCoef() <= degree;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSaturated(const aux::predicate<Lit>& toWeaken) const {
  SMALL largest = 0;
  LARGE weakenedDeg = degree;
  for (Var v : vars) {
    SMALL cf = aux::abs(coefs[v]);
    if (toWeaken(getLit(v))) {
      weakenedDeg -= cf;
    } else {
      largest = std::max(largest, cf);
    }
  }
  return largest <= weakenedDeg;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::getSaturatedLits(IntSet& out) const {
  if (getLargestCoef() < degree) return;  // no saturated lits
  SMALL smalldeg = aux::cast<SMALL>(degree);
  for (Var v : vars) {
    if (aux::abs(coefs[v]) >= smalldeg) out.add(getLit(v));
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::invert() {
  rhs = -rhs;
  for (Var v : vars) coefs[v] = -coefs[v];
  degree = calcDegree();
}

/*
 * Fixes overflow
 * @pre @post: hasNoZeroes()
 * @pre @post: isSaturated()
 * @post: nothing else if bitOverflow == 0
 * @post: the largest coefficient is less than 2^bitOverflow
 * @post: the degree and rhs are less than 2^bitOverflow * INF
 * @post: if overflow happened, all division until 2^bitReduce happened
 * @post: the constraint remains conflicting or propagating on asserting
 *
 * NOTE: largestCoef sometimes is the largest coef "to be checked".
 * If larger coefs exist, no overflow should be possible.
 */
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::fixOverflow(const IntMap<int>& level, int bitOverflow, int bitReduce,
                                          const SMALL& largestCoef, Lit asserting) {
  assert(hasNoZeroes());
  assert(isSaturated());
  if (bitOverflow == 0) {
    return;
  }
  assert(bitOverflow > 0);
  assert(bitReduce > 0);
  assert(bitOverflow >= bitReduce);
  LARGE maxVal = std::max<LARGE>(largestCoef, std::max(degree, aux::abs(rhs)) / INF);
  if (maxVal > 0 && (int)aux::msb(maxVal) >= bitOverflow) {
    assert(getCutoffVal() == maxVal);
    LARGE div = aux::ceildiv<LARGE>(maxVal, aux::powtwo<LARGE>(bitReduce) - 1);
    assert(aux::ceildiv<LARGE>(maxVal, div) <= aux::powtwo<LARGE>(bitReduce) - 1);
    weakenDivideRound(div, [&](Lit l) { return !isFalse(level, l) && l != -asserting && l != asserting; });
  } else {
    // check that largestCoef indeed is big enough
    assert(getCutoffVal() <= 0 || (int)aux::msb(getCutoffVal()) < bitOverflow);
  }
  assert(isSaturated());
  assert(hasNoZeroes());
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturateAndFixOverflow(const IntMap<int>& level, int bitOverflow, int bitReduce,
                                                     Lit asserting) {
  assert(hasNoZeroes());
  SMALL largest = getLargestCoef();
  if (largest > degree) {
    saturate(false, false);
    largest = static_cast<SMALL>(degree);
  }
  fixOverflow(level, bitOverflow, bitReduce, largest, asserting);
}

/*
 * Fixes overflow for rationals
 * @post: saturated
 * @post: none of the coefficients, degree, or rhs exceed INFLPINT
 */
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::saturateAndFixOverflowRational() {
  removeZeroes();
  LARGE maxRhs = std::max(getDegree(), aux::abs(getRhs()));
  // TODO: why do we look at degree and not max coefficient here?
  while (maxRhs >= INFLPINT) {
    LARGE d = aux::ceildiv<LARGE>(maxRhs, INFLPINT - 1);
    assert(d >= 2);
    divideRoundUp(d);
    saturate(true, false);
    maxRhs = std::max(getDegree(), aux::abs(getRhs()));
    // NOTE: due to cumulative round-off errors, we may not always have a sufficient small rhs/degree
    // so we keep dividing by at least two until we get there
  }
  assert(getDegree() < INFLPINT);
  assert(aux::abs(getRhs()) < INFLPINT);
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::fitsInDouble() const {
  return isSaturated() && degree < INFLPINT && rhs < INFLPINT;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::largestCoefFitsIn(int bits) const {
  return (int)aux::msb(getLargestCoef()) < bits;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::multiply(const SMALL& m) {
  assert(m > 0);
  if (m == 1) return;
  if (global.logger.isActive()) Logger::proofMult(proofBuffer, m);
  for (Var v : vars) coefs[v] *= m;
  rhs *= m;
  degree *= m;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::divideRoundUp(const LARGE& d) {
  assert(d > 0);
  if (d == 1) return;
  if (global.logger.isActive()) Logger::proofDiv(proofBuffer, d);
  for (Var v : vars) {
    // divides away from zero
    bool undivisible = coefs[v] % d != 0;
    coefs[v] = static_cast<SMALL>(coefs[v] / d) + (coefs[v] > 0 && undivisible) - (coefs[v] < 0 && undivisible);
  }
  degree = aux::ceildiv(degree, d);
  rhs = calcRhs();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::divideRoundDown(const LARGE& d) {
  assert(d > 0);
  if (d == 1) return;
  for (Var v : vars) {
    weaken(-static_cast<SMALL>(coefs[v] % d), v);
    assert(coefs[v] % d == 0);
    coefs[v] = static_cast<SMALL>(coefs[v] / d);
  }
  if (global.logger.isActive()) Logger::proofDiv(proofBuffer, d);
  degree = degree <= 0 ? 0 : aux::ceildiv(degree, d);
  rhs = calcRhs();
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenDivideRound(const LARGE& div, const aux::predicate<Lit>& toWeaken) {
  assert(div > 0);
  if (div == 1) return;
  weakenNonDivisible(toWeaken, div);
  if (isTautology()) {
    saturate(false, false);
    removeZeroes();
  } else {
    weakenSuperfluous(div, false, []([[maybe_unused]] Var v) { return true; });
    removeZeroes();
    divideRoundUp(div);
    saturate(true, false);
  }
}

// NOTE: preserves ordered-ness
// div is a divisor
// toWeaken tells how to weaken the non-divisible literals
// toWeakenSuperfluous tells how to weaken superfluous literals (if any, if needed)
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenDivideRoundOrdered(const LARGE& div, const IntMap<int>& level) {
  assert(isSortedInDecreasingCoefOrder());
  assert(div > 0);
  if (div == 1) return;
  weakenNonDivisible(div, level);
  // std::cout << "weakened non divisible" << std::endl;
  // toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;
  weakenSuperfluous(div);
  repairOrder();
  while (!vars.empty() && coefs[vars.back()] == 0) {
    popLast();
  }
  assert(hasNoZeroes());
  
  // std::cout << "in weakenDivideRoundOrdered: " << std::endl;
  // toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;
  if (div >= degree) {
    simplifyToClause();
  } else if (!vars.empty() && div >= aux::abs(coefs[vars[0]])) {
    simplifyToCardinality(false, getCardinalityDegree());
  } else {
    divideRoundUp(div);
    saturate(true, true);
  }
}

// NOTE: preserves ordered-ness
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenDivideRoundOrderedCanceling(const LARGE& div, const IntMap<int>& level,
                                                                const std::vector<int>& pos, const SMALL& mult,
                                                                const ConstrExp<SMALL, LARGE>& confl) {
  assert(isSortedInDecreasingCoefOrder());
  assert(div > 0);
  if (div == 1) return;
  weakenNonDivisibleCanceling(div, level, mult, confl);
  weakenSuperfluousCanceling(div, pos);
  repairOrder();
  while (!vars.empty() && coefs[vars.back()] == 0) {
    popLast();
  }
  assert(hasNoZeroes());
  if (div >= degree) {
    simplifyToClause();
  } else if (!vars.empty() && div >= aux::abs(coefs[vars[0]])) {
    simplifyToCardinality(false, getCardinalityDegree());
  } else {
    divideRoundUp(div);
    saturate(true, true);
  }
}

// NOTE: does not preserve order, as the asserting literal is skipped and some literals are partially weakened
// NOTE: after call to weakenNonDivisible, order can be re repaired by call to repairOrder
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonDivisible(const aux::predicate<Lit>& toWeaken, const LARGE& div) {
  assert(div > 0);
  if (div == 1) return;
  for (Var v : vars) {
    if (coefs[v] % div != 0 && toWeaken(getLit(v))) {
      weaken(-static_cast<SMALL>(coefs[v] % div), v);
    }
  }
}

// NOTE: does not preserve order, as the asserting literal is skipped and some literals are partially weakened
// NOTE: after call to weakenNonDivisible, order can be re repaired by call to repairOrder
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonDivisible(const LARGE& div, const IntMap<int>& level) {
  assert(div > 0);
  if (div == 1) return;
  for (Var v : vars) {
    if (coefs[v] % div != 0 && !isFalse(level, getLit(v))) {
      weaken(-static_cast<SMALL>(coefs[v] % div), v);
    }
  }
}

// NOTE: does not preserve order, as the asserting literal is skipped and some literals are partially weakened
// NOTE: after call to weakenNonDivisible, order can be re repaired by call to repairOrder
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonDivisibleCanceling(const LARGE& div, const IntMap<int>& level, const SMALL& mult,
                                                          const ConstrExp<SMALL, LARGE>& confl) {
  assert(div > 0);
  if (div == 1) return;
  for (Var v : vars) {
    Lit l = getLit(v);
    if (coefs[v] % div != 0 && !isFalse(level, l) && (isTrue(level, l) || confl.getCoef(-l) < mult)) {
      weaken(-static_cast<SMALL>(coefs[v] % div), v);
    }
  }
}

// NOTE: should only be used in conjunction with weakenNonDivisible
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::repairOrder() {
  int i = 1;
  int j = 0;
  for (; i < nVars(); ++i) {
    SMALL back = aux::abs(coefs[vars[i]]);
    SMALL front = aux::abs(coefs[vars[j]]);
    if (back > front) {
      std::swap(vars[i], vars[j]);
      index[vars[i]] = i;
      index[vars[j]] = j;
      ++j;
    } else if (front > back) {
      j = i;
    }
    assert(aux::abs(coefs[vars[i]]) == aux::abs(coefs[vars[j]]));
  }
  assert(isSortedInDecreasingCoefOrder());
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenSuperfluous(const LARGE& div, bool sorted, const aux::predicate<Var>& toWeaken) {
  assert(div > 1);
  assert(!isTautology());
  [[maybe_unused]] LARGE quot = aux::ceildiv(degree, div);
  LARGE rem = (degree - 1) % div;
  if (!sorted) {                                             // extra iteration to weaken literals fully
    for (int i = vars.size() - 1; i >= 0 && rem > 0; --i) {  // going back to front in case the coefficients are sorted
      Var v = vars[i];
      if (!toWeaken(v) || coefs[v] == 0) continue;
      SMALL r = aux::abs(coefs[v]);
      if (r <= rem) {
        rem -= r;
        weaken(v);
      }
    }
  }
  for (int i = vars.size() - 1; i >= 0 && rem > 0; --i) {  // going back to front in case the coefficients are sorted
    Var v = vars[i];
    if (!toWeaken(v) || coefs[v] == 0 || saturatedVar(v)) continue;
    SMALL r = static_cast<SMALL>(static_cast<LARGE>(aux::abs(coefs[v])) % div);
    if (r <= rem) {
      rem -= r;
      weaken(coefs[v] < 0 ? r : -r, v);
    }
  }
  assert(quot == aux::ceildiv(degree, div));
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenSuperfluous(const LARGE& div) {
  assert(div > 1);
  assert(!isTautology());
  [[maybe_unused]] LARGE quot = aux::ceildiv(degree, div);
  LARGE rem = (degree - 1) % div;
  for (int i = vars.size() - 1; i >= 0 && rem > 0; --i) {  // going back to front in case the coefficients are sorted
    Var v = vars[i];
    if (coefs[v] == 0 || saturatedVar(v)) continue;
    SMALL r = static_cast<SMALL>(static_cast<LARGE>(aux::abs(coefs[v])) % div);
    if (r <= rem) {
      rem -= r;
      weaken(coefs[v] < 0 ? r : -r, v);
    }
  }
  assert(quot == aux::ceildiv(degree, div));
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenSuperfluousCanceling(const LARGE& div, const std::vector<int>& pos) {
  assert(div > 1);
  assert(!isTautology());
  [[maybe_unused]] LARGE quot = aux::ceildiv(degree, div);
  LARGE rem = (degree - 1) % div;
  for (int i = vars.size() - 1; i >= 0 && rem > 0; --i) {  // going back to front in case the coefficients are sorted
    Var v = vars[i];
    if (pos[v] == INF || coefs[v] == 0 || saturatedVar(v)) continue;
    SMALL r = static_cast<SMALL>(static_cast<LARGE>(aux::abs(coefs[v])) % div);
    if (r <= rem) {
      rem -= r;
      weaken(coefs[v] < 0 ? r : -r, v);
    }
  }
  assert(quot == aux::ceildiv(degree, div));
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::applyMIR(const LARGE& d, const std::function<Lit(Var)>& toLit) {
  assert(d > 0);
  LARGE tmpRhs = rhs;
  for (Var v : vars)
    if (toLit(v) < 0) tmpRhs -= coefs[v];
  LARGE bmodd = aux::mod_safe(tmpRhs, d);
  rhs = bmodd * aux::ceildiv_safe(tmpRhs, d);
  for (Var v : vars) {
    if (toLit(v) < 0) {
      coefs[v] = static_cast<SMALL>(
          -(bmodd * aux::floordiv_safe<LARGE>(-coefs[v], d) + std::min(aux::mod_safe<LARGE>(-coefs[v], d), bmodd)));
      rhs += coefs[v];
    } else
      coefs[v] = static_cast<SMALL>(bmodd * aux::floordiv_safe<LARGE>(coefs[v], d) +
                                    std::min(aux::mod_safe<LARGE>(coefs[v], d), bmodd));
  }
  degree = calcDegree();
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::divideByGCD() {
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  if (vars.empty()) return false;
  SMALL _gcd = aux::abs(coefs[vars.back()]);
  if (_gcd == 1) return false;
  for (Var v : vars) {
    if (saturatedVar(v)) continue;
    _gcd = aux::gcd(_gcd, aux::abs(coefs[v]));
    if (_gcd == 1) return false;
  }
  assert(_gcd > 1);
  divideRoundUp(_gcd);
  return true;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::divideTo(double limit, const aux::predicate<Lit>& toWeaken) {
  LARGE maxVal = getCutoffVal();
  if (maxVal <= static_cast<LARGE>(limit)) {
    return false;
  }
  LARGE div = aux::ceildiv(maxVal, static_cast<LARGE>(limit));  // maxVal / div =< limit
  assert(div > 1);
  weakenDivideRound(div, toWeaken);  // TODO: weakenDivideRoundOrdered?
  return true;
}

// NOTE: only equivalence preserving operations over the Bools!
void ConstrExpSuper::postProcess(const IntMap<int>& level, const std::vector<int>& pos, const Heuristic& heur,
                                 bool sortFirst, Stats& stats) {
  removeUnitsAndZeroes(level, pos);
  assert(sortFirst || isSortedInDecreasingCoefOrder());  // NOTE: check this only after removing units and zeroes
  saturate(true, !sortFirst);
  if (isClause() || isCardinality()) return;
  if (sortFirst) {
    const std::vector<ActNode>& actList = heur.getActList();
    sortInDecreasingCoefOrder([&](Var v1, Var v2) { return actList[v1].activity > actList[v2].activity; });
  }
  if (divideByGCD()) {
    ++stats.NGCD;
  }
  if (simplifyToCardinality(true, getCardinalityDegree())) {
    ++stats.NCARDDETECT;
  }
}

void ConstrExpSuper::strongPostProcess(Solver& solver) {
  [[maybe_unused]] int nvars = nNonZeroVars();
  removeEqualities(solver.getEqualities(), true);
  selfSubsumeImplications(solver.getImplications());
  postProcess(solver.getLevel(), solver.getPos(), solver.getHeuristic(), true, solver.getStats());
  assert(nvars >= nNonZeroVars());
}

template <typename SMALL, typename LARGE>
AssertionStatus ConstrExp<SMALL, LARGE>::isAssertingBefore(const IntMap<int>& level, int lvl) const {
  assert(lvl >= 0);
  assert(isSaturated());
  SMALL largestCoef = 0;
  LARGE slack = -degree;
  for (int i = vars.size() - 1; i >= 0 && slack < degree; --i) {  // maybe higher-level coefficients reside in the back
    Var v = vars[i];
    Lit l = coefs[v] < 0 ? -v : v;
    if (level[-l] < lvl) continue;  // falsified lit
    SMALL c = aux::abs(coefs[v]);
    if (level[l] >= lvl) largestCoef = std::max(largestCoef, c);  // unknown lit
    slack += c;
  }
  if (slack >= largestCoef) {
    return AssertionStatus::NONASSERTING;
  } else if (slack >= 0) {
    return AssertionStatus::ASSERTING;
  } else {
    return AssertionStatus::FALSIFIED;
  }
}

// @return: highest decision level that does not make the constraint inconsistent
// @return: whether or not the constraint is asserting at that level
template <typename SMALL, typename LARGE>
std::pair<int, bool> ConstrExp<SMALL, LARGE>::getAssertionStatus(const IntMap<int>& level, const std::vector<int>& pos,
                                                                 std::vector<Lit>& litsByPos) const {
  assert(hasNoZeroes());
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoUnits(level));
  assert(litsByPos.empty());
  // calculate slack at level 0
  LARGE slack = -degree;
  for (Var v : vars) slack += aux::abs(coefs[v]);
  if (slack < 0) return {-1, false};

  // create useful datastructures
  for (Var v : vars) {
    Lit l = getLit(v);
    assert(l != 0);
    if (isFalse(level, l)) litsByPos.push_back(-l);
  }
  std::sort(litsByPos.begin(), litsByPos.end(), [&](Lit l1, Lit l2) { return pos[toVar(l1)] < pos[toVar(l2)]; });

  // calculate earliest propagating decision level by decreasing slack one decision level at a time
  auto posIt = litsByPos.cbegin();
  auto coefIt = vars.cbegin();
  int assertionLevel = 0;
  while (true) {
    while (posIt != litsByPos.cend() && level[*posIt] <= assertionLevel) {
      slack -= aux::abs(coefs[aux::abs(*posIt)]);
      ++posIt;
    }
    if (slack < 0) {
      litsByPos.clear();
      return {assertionLevel - 1, false};  // not asserting, but earliest non-conflicting level
    }
    while (coefIt != vars.cend() && assertionLevel >= level[getLit(*coefIt)]) ++coefIt;
    if (coefIt == vars.cend()) {
      litsByPos.clear();
      return {INF, false};
    }
    if (slack < aux::abs(coefs[*coefIt])) {
      litsByPos.clear();
      return {assertionLevel, true};
    }
    if (posIt == litsByPos.cend()) {
      litsByPos.clear();
      return {INF, false};
    }
    assertionLevel = level[*posIt];
  }
}

// @post: preserves order after removeZeroes()
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonImplied(const IntMap<int>& level, const LARGE& slack) {
  int weakenings = 0;
  for (Var v : vars) {
    if (coefs[v] != 0 && aux::abs(coefs[v]) <= slack && !falsified(level, v)) {
      weaken(v);
      ++weakenings;
    }
  }
  global.stats.NWEAKENEDNONIMPLIED += weakenings;
}

// @post: preserves order after removeZeroes()
// TODO: return modified slack?
template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::weakenNonImplying(const IntMap<int>& level, const SMALL& propCoef, const LARGE& slack) {
  LARGE slk = slack;
  assert(hasNoZeroes());
  assert(isSortedInDecreasingCoefOrder());
  int weakenings = 0;
  for (int i = vars.size() - 1; i >= 0 && slk + aux::abs(coefs[vars[i]]) < propCoef; --i) {
    Var v = vars[i];
    if (falsified(level, v)) {
      slk += aux::abs(coefs[v]);
      weaken(v);
      ++weakenings;
    }
  }
  global.stats.NWEAKENEDNONIMPLYING += weakenings;
  return weakenings != 0;
}

// @post: preserves order after removeZeroes()
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::weakenNonFalsified(const IntMap<int>& level, const SMALL& amount, const Lit& asserting) {
  SMALL am = amount;
  // std::cout << "in weakenNonFalsified: " << std::endl;
  // std::cout << "amount: " << amount << std::endl;
  assert(hasNoZeroes());
  assert(isSortedInDecreasingCoefOrder());
  // assert(getSlack(level) >= 0);
  for (int i = vars.size() - 1; i >= 0 && am > 0; --i) {
    Var v = vars[i];
    if (coefs[v] != 0 && !falsified(level, v) && getLit(v) != asserting) {
      if (aux::abs(coefs[v]) < am) { 
        am -= aux::abs(coefs[v]);
        // std::cout << "weakened: " << v << std::endl;
        // std::cout << "coefs[v]: " << coefs[v] << std::endl;
        // std::cout << "am: " << am << std::endl;
        weaken(v); 
      } else { 
        // std::cout << "weakened partially: " << v << std::endl;
        // std::cout << "coefs[v]: " << coefs[v] << std::endl;
        // std::cout << "am: " << am << std::endl;
        weaken(coefs[v] < 0 ? am : -am, v);
        am = 0;
        removeZeroes();
        fixOrderAtIndex(i); 
      }
    }
  }
  // std::cout << "asserting in weakenNonFalsified: " << asserting << std::endl;
  // std::cout << "after weakening: " << std::endl;
  // toStreamPure(std::cout);
  // std::cout << "\n" << std::endl;
  assert(am == 0);
  assert(isSortedInDecreasingCoefOrder());
}

// @post: preserves order after removeZeroes()
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::heuristicWeakening(const IntMap<int>& level, const std::vector<int>& pos) {
  assert(isSortedInDecreasingCoefOrder());
  if (aux::abs(coefs[vars[0]]) == aux::abs(coefs[vars.back()])) return;
  LARGE slk = getSlack(level);
  if (slk < 0) return;  // no propagation, no idea what to weaken
  Var v_prop = -1;
  for (int i = vars.size() - 1; i >= 0; --i) {
    Var v = vars[i];
    if (aux::abs(coefs[v]) > slk && isUnknown(pos, v)) {
      v_prop = v;
      break;
    }
  }
  if (v_prop == -1) return;  // no propagation, no idea what to weaken
  if (global.options.weakenNonImplying) {
    if (weakenNonImplying(level, aux::abs(coefs[v_prop]), slk)) {
      slk = getSlack(level);  // slack changed
    }
  }
  assert(slk < aux::abs(coefs[v_prop]));
  weakenNonImplied(level, slk);
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::absCoeffSum() const {
  LARGE result = 0;
  for (Var v : vars) result += aux::abs(coefs[v]);
  return result;
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::simplifyToCardinality(bool equivalencePreserving, int cardDegree) {
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  assert(!equivalencePreserving || isSaturated());

  if (vars.empty() || aux::abs(coefs[vars[0]]) == 1) return false;
  if (cardDegree <= 0) {
    saturate(true, true);
    return false;
  }
  assert(cardDegree <= nVars());

  if (equivalencePreserving) {
    LARGE smallCoefSum = 0;
    for (int i = 1; i <= cardDegree; ++i) {
      smallCoefSum += aux::abs(coefs[vars[nVars() - i]]);
    }
    if (smallCoefSum < degree) return false;
    // else, we have an equivalent cardinality constraint
  }

  if (cardDegree == 1) {
    simplifyToClause();
    return true;
  }
  SMALL cardCoef = aux::abs(coefs[vars[cardDegree - 1]]);
  for (int i = 0; i < cardDegree - 1; ++i) {
    Var v = vars[i];
    if (coefs[v] < 0) {
      weaken(-cardCoef - coefs[v], v);
    } else {
      weaken(cardCoef - coefs[v], v);
    }
  }
  assert(cardCoef == getLargestCoef());
  LARGE cardSum = static_cast<LARGE>(cardDegree - 1) * cardCoef;
  assert(degree > cardSum);
  while (nVars() > cardDegree && (degree - aux::abs(coefs[vars.back()]) > cardSum)) {
    weakenLast();
  }
  assert(cardSum + cardCoef >= degree);
  divideRoundUp(cardCoef);
  assert(isCardinality());
  assert(degree == cardDegree);

  return true;
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isCardinality() const {
  return std::all_of(vars.cbegin(), vars.cend(), [&](Var v) { return aux::abs(coefs[v]) <= 1; });
}

template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::getCardinalityDegree() const {
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  if (vars.empty()) return degree > 0;
  if (degree == 1) return 1;
  if (aux::abs(coefs[vars[0]]) == 1) return static_cast<int>(degree);
  LARGE coefsum = -degree;
  int i = 0;
  for (; i < (int)vars.size() && coefsum < 0; ++i) {
    coefsum += aux::abs(coefs[vars[i]]);
  }
  return i;
}

template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::getMaxStrengthCardinalityDegree(std::vector<int>& cardPoints) const {
  if (vars.empty() == 0) return degree > 0;
  if (degree == 1) return 1;
  if (aux::abs(coefs[vars[0]]) == 1) return static_cast<int>(degree);
  getCardinalityPoints(cardPoints);
  int bestCardDegree = 0;
  double bestStrength = 0;
  for (int i = 0; i < (int)cardPoints.size(); ++i) {
    double strength = (cardPoints.size() - i) / (double)(cardPoints[i] + 1);
    if (bestStrength < strength) {
      bestStrength = strength;
      bestCardDegree = cardPoints.size() - i;
    }
  }

  assert(bestCardDegree > 0);
  assert(bestStrength > 0);
  assert(bestStrength <= 1);
  return bestCardDegree;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::getCardinalityPoints(std::vector<int>& cardPoints) const {
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  LARGE coefsum = 0;
  int cardDegree = 0;
  for (; cardDegree < (int)vars.size() && coefsum < degree; ++cardDegree) {
    coefsum += aux::abs(coefs[vars[cardDegree]]);
  }
  cardPoints.clear();
  cardPoints.reserve(cardDegree);

  LARGE weakenedDegree = degree;
  int varsLeft = nVars();
  coefsum -= aux::abs(coefs[vars[cardDegree - 1]]);
  while (weakenedDegree > 0 && cardDegree > 0 && varsLeft > 0) {
    --varsLeft;
    weakenedDegree -= aux::abs(coefs[vars[varsLeft]]);
    assert(index[vars[varsLeft]] == varsLeft);
    if (weakenedDegree <= coefsum) {
      --cardDegree;
      coefsum -= aux::abs(coefs[vars[cardDegree - 1]]);
      cardPoints.push_back(varsLeft);
    }
  }
}

// @pre: sorted in *IN*creasing coef order, so that we can pop zero coefficient literals
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::getCardinalityDegreeWithZeroes() {
  LARGE coefsum = -degree;
  int carddegree = 0;
  int i = vars.size() - 1;
  for (; i >= 0 && coefsum < 0; --i) {
    if (coefs[vars[i]] != 0) {
      coefsum += aux::abs(coefs[vars[i]]);
      ++carddegree;
    }
  }
  ++i;
  [[maybe_unused]] int newsize = i + carddegree;
  int j = i;
  for (; i < (int)vars.size(); ++i) {
    Var v = vars[i];
    if (coefs[v] != 0) {
      index[v] = j;
      vars[j++] = v;
    } else {
      index[v] = -1;
    }
  }
  vars.resize(j);
  assert(newsize == (int)vars.size());
  return carddegree;
}

// @post: preserves order of vars
template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::simplifyToClause() {
  assert(isSortedInDecreasingCoefOrder());
  assert(hasNoZeroes());
  while (!vars.empty() && aux::abs(coefs[vars.back()]) < degree) {
    weakenLast();
  }
  if (!vars.empty()) divideRoundUp(aux::abs(coefs[vars[0]]));
  assert(vars.empty() || degree <= 1);
  assert(isClause());
  assert(hasNoZeroes());
}

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isClause() const {
  return degree == 1;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::simplifyToUnit(const IntMap<int>& level, const std::vector<int>& pos, Var v_unit) {
  removeUnitsAndZeroes(level, pos);
  assert(getLit(v_unit) != 0);
  for (Var v : vars) {
    if (v != v_unit) weaken(v);
  }
  removeZeroes();
  saturate(true, false);
  assert(degree > 0);
  divideRoundUp(std::max<LARGE>(aux::abs(coefs[v_unit]), degree));
  assert(isUnitConstraint());
}

template <typename SMALL, typename LARGE>
LARGE ConstrExp<SMALL, LARGE>::getNonFalsified(const IntMap<int>& level, const Lit& asserting) const {
  LARGE result = 0;
  for (Var v : getVars()) {
    if (!falsified(level, v) && getLit(v) != asserting) result += aux::abs(getCoef(v));
  }
  return result;
}

bool ConstrExpSuper::isUnitConstraint() const { return isClause() && nVars() == 1 && !isInconsistency(); }

template <typename SMALL, typename LARGE>
bool ConstrExp<SMALL, LARGE>::isSortedInDecreasingCoefOrder() const {
  if (vars.size() <= 1) return true;
  SMALL first = aux::abs(coefs[vars[0]]);
  SMALL second = 0;
  for (int i = 1; i < (int)vars.size(); ++i) {
    second = aux::abs(coefs[vars[i]]);
    if (first < second) return false;
    first = std::move(second);
  }
  return true;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::sortInDecreasingCoefOrder(const std::function<bool(Var, Var)>& tiebreaker) {
  if (vars.size() <= 1 || isSortedInDecreasingCoefOrder()) return;
  std::sort(vars.begin(), vars.end(), [&](Var v1, Var v2) {
    int res = aux::sgn(aux::abs(coefs[v1]) - aux::abs(coefs[v2]));
    return res > 0 || (res == 0 && tiebreaker(v1, v2));
  });
  for (int i = 0; i < (int)vars.size(); ++i) index[vars[i]] = i;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::sortWithCoefTiebreaker(const std::function<int(Var, Var)>& comp) {
  if (vars.size() <= 1) return;
  std::sort(vars.begin(), vars.end(), [&](Var v1, Var v2) {
    int res = comp(v1, v2);
    return res > 0 || (res == 0 && aux::abs(coefs[v1]) > aux::abs(coefs[v2]));
  });
  for (int i = 0; i < (int)vars.size(); ++i) index[vars[i]] = i;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::fixOrderAtIndex(const int index) {
  assert(index >= 0 && index < (int)vars.size());
  Var checking = vars[index];
  SMALL checkingCoef = absCoef(checking);
  for (int i = index; i < vars.size() - 1 && absCoef(vars[i+1]) > checkingCoef; i++) {
    std::swap(vars[i], vars[i + 1]);
  }
  assert(isSortedInDecreasingCoefOrder());
}

int ConstrExpSuper::nNonZeroVars() const {
  int result = 0;
  for (Var v : vars) {
    result += hasVar(v);
  }
  return result;
}

void ConstrExpSuper::reverseOrder() {
  std::reverse(vars.begin(), vars.end());
  for (int i = 0; i < (int)vars.size(); ++i) index[vars[i]] = i;
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamAsOPBlhs(std::ostream& o, bool withConstant) const {
  std::vector<Var> vs = vars;
  std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vs) {
    Lit l = getLit(v);
    if (l == 0) continue;
    o << std::pair<SMALL, Lit>{getCoef(l), l} << " ";
  }
  if (withConstant && degree != 0) {
    o << "-" << degree << " 1 ";
  }
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamAsOPB(std::ostream& o) const {
  toStreamAsOPBlhs(o, false);
  o << ">= " << degree << " ;";
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamWithAssignment(std::ostream& o, const IntMap<int>& level,
                                                     const std::vector<int>& pos) const {
  std::vector<Var> vs = vars;
  std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vs) {
    Lit l = getLit(v);
    if (l == 0) continue;
    o << getCoef(l) << "x" << l
      << (isUnknown(pos, l) ? "u"
                            : (isFalse(level, l) ? "f" + std::to_string(level[-l]) : "t" + std::to_string(level[l])))
      << " ";
  }
  o << ">= " << degree << " (" << getSlack(level) << ")";
}

template <typename SMALL, typename LARGE>
void ConstrExp<SMALL, LARGE>::toStreamPure(std::ostream& o) const {
  std::vector<Var> vs = vars;
  for (Var v : vs) {
    Lit l = getLit(v);
    o << (l == 0 ? std::pair<SMALL, Lit>{0, v} : std::pair<SMALL, Lit>{getCoef(l), l}) << " ";
  }
  std::cout << ">= " << degree << " (" << rhs << ")";
}

template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  assert(getCoef(-l) > 0);
  assert(hasNoZeroes());
  global.stats.NADDEDLITERALS += size;

  for (unsigned int i = 0; i < size; ++i) {
    Lit ll = data[i];
    if (isFalse(level, ll)) {
      actSet.add(toVar(ll));
    }
  }

  LARGE oldDegree = getDegree();
  SMALL largestCF = 0;
  SMALL cmult = getCoef(-l);
  assert(cmult >= 1);
  if (global.logger.isActive()) {
    Logger::proofMult(proofBuffer << id << " ", cmult) << "+ ";
    for (unsigned int i = 0; i < size; ++i) {
      Lit ll = data[i];
      if (isUnit(level, ll)) {
        Logger::proofWeaken(proofBuffer, ll, -cmult);
      } else if (isUnit(level, -ll)) {
        Logger::proofWeakenFalseUnit(proofBuffer, global.logger.getUnitID(pos[toVar(ll)]), -cmult);
      }
    }
  }
  addRhs(cmult * deg);
  for (unsigned int i = 0; i < size; ++i) {
    Lit ll = data[i];
    if (isUnit(level, -ll)) {
      continue;
    }
    if (isUnit(level, ll)) {
      addRhs(-cmult);
      continue;
    }
    Var v = toVar(ll);
    SMALL cf = cmult;
    if (ll < 0) {
      rhs -= cmult;
      cf = -cmult;
    }
    add(v, cf, true);
    largestCF = std::max(largestCF, aux::abs(coefs[v]));
  }

  assert(getDegree() > 0);
  if (oldDegree <= getDegree()) {
    if (largestCF > getDegree()) {
      global.stats.NSATURATESTEPS += size;
      if (global.logger.isActive()) proofBuffer << "s ";
      largestCF = static_cast<SMALL>(degree);
      for (unsigned int i = 0; i < size; ++i) {
        Var v = toVar(data[i]);
        if (coefs[v] < -largestCF) {
          rhs -= coefs[v] + largestCF;
          coefs[v] = -largestCF;
        } else {
          coefs[v] = std::min(coefs[v], largestCF);
        }
      }
    }
    fixOverflow(level, global.options.bitsOverflow.get(), global.options.bitsReduced.get(), largestCF, 0);
  } else {
    saturateAndFixOverflow(level, global.options.bitsOverflow.get(), global.options.bitsReduced.get(), 0);
  }
  assert(getCoef(-l) == 0);
  assert(hasNegativeSlack(level));

  IntSet& lbdSet = global.isPool.take();
  for (int i = 0; i < (int)size; ++i) {
    lbdSet.add(level[-data[i]] % INF);
  }
  lbdSet.remove(0);  // unit literals and non-falsifieds should not be counted
  int lbd = lbdSet.size();
  global.isPool.release(lbdSet);
  return lbd;
}

//@post: variable vector vars is not changed, but coefs[toVar(toSubsume)] may become 0
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const Lit* data, unsigned int size, unsigned int deg, ID id, Lit toSubsume,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  assert(isSaturated());
  assert(getCoef(-toSubsume) > 0);
  global.stats.NADDEDLITERALS += size;

  int weakenedDeg = deg;
  assert(weakenedDeg > 0);
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i];
    if (l != toSubsume && !isUnit(level, -l) && !saturatedLits.has(l)) {
      --weakenedDeg;
      if (weakenedDeg <= 0) {
        return 0;
      }
    }
  }
  assert(weakenedDeg > 0);
  SMALL& cf = coefs[toVar(toSubsume)];
  const SMALL mult = aux::abs(cf);
  if (cf < 0) {
    rhs -= cf;
  }
  cf = 0;
  saturatedLits.remove(-toSubsume);
  ++global.stats.NSUBSUMESTEPS;

  if (global.logger.isActive()) {
    proofBuffer << id << " ";
    for (unsigned int i = 0; i < size; ++i) {
      Lit l = data[i];
      if (isUnit(level, l)) {
        Logger::proofWeaken(proofBuffer, l, -1);
      } else if (isUnit(level, -l)) {
        Logger::proofWeakenFalseUnit(proofBuffer, global.logger.getUnitID(pos[toVar(l)]), -1);
      }
    }
    for (int i = 0; i < (int)size; ++i) {
      Lit l = data[i];
      if (l != toSubsume && !isUnit(level, -l) && !isUnit(level, l) && !saturatedLits.has(l)) {
        Logger::proofWeaken(proofBuffer, l, -1);
      }
    }
    // saturate, multiply, divide, add, saturate
    Logger::proofMult(proofBuffer, mult) << "+ s ";
  }

  IntSet& lbdSet = global.isPool.take();
  for (int i = 0; i < (int)size; ++i) {
    Lit l = data[i];
    if (l == toSubsume || saturatedLits.has(l)) {
      lbdSet.add(level[-l] % INF);
    }
  }
  lbdSet.remove(0);  // unit literals and non-falsifieds should not be counted
  int lbd = lbdSet.size();
  assert(lbd > 0);
  global.isPool.release(lbdSet);
  return lbd;
}

template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Origin o,
                                         Lit l, const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  return genericResolve(terms, size, degr, id, o, l, level, pos, actSet);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Origin o,
                                         Lit l, const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  return genericResolve(terms, size, degr, id, o, l, level, pos, actSet);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Origin o,
                                         Lit l, const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  return genericResolve(terms, size, degr, id, o, l, level, pos, actSet);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Origin o,
                                         Lit l, const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  return genericResolve(terms, size, degr, id, o, l, level, pos, actSet);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::resolveWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Origin o,
                                         Lit l, const IntMap<int>& level, const std::vector<int>& pos, IntSet& actSet) {
  return genericResolve(terms, size, degr, id, o, l, level, pos, actSet);
}

template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const Term32* terms, unsigned int size, const long long& degr, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  return genericSubsume(terms, size, degr, id, l, level, pos, saturatedLits);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const Term64* terms, unsigned int size, const int128& degr, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  return genericSubsume(terms, size, degr, id, l, level, pos, saturatedLits);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const Term128* terms, unsigned int size, const int128& degr, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  return genericSubsume(terms, size, degr, id, l, level, pos, saturatedLits);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const Term128* terms, unsigned int size, const int256& degr, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  return genericSubsume(terms, size, degr, id, l, level, pos, saturatedLits);
}
template <typename SMALL, typename LARGE>
int ConstrExp<SMALL, LARGE>::subsumeWith(const TermArb* terms, unsigned int size, const bigint& degr, ID id, Lit l,
                                         const IntMap<int>& level, const std::vector<int>& pos, IntSet& saturatedLits) {
  return genericSubsume(terms, size, degr, id, l, level, pos, saturatedLits);
}

template struct ConstrExp<int, long long>;
template struct ConstrExp<long long, int128>;
template struct ConstrExp<int128, int128>;
template struct ConstrExp<int128, int256>;
template struct ConstrExp<bigint, bigint>;

}  // namespace xct
