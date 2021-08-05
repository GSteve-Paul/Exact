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

#include "aux.hpp"

namespace rs {

using ID = uint64_t;
const ID ID_Undef = std::numeric_limits<ID>::max();
const ID ID_Unsat = ID_Undef - 1;
const ID ID_Trivial = 1;  // represents constraint 0 >= 0
inline bool isValid(ID id) { return id > 0 && id < ID_Unsat; }

using Var = int;
using Lit = int;
inline Var toVar(Lit l) { return std::abs(l); }

const int resize_factor = 2;

const int INF = 1e9 + 1;  // 1e9 < 30 bits is the maximum number of variables in the system, anything beyond is infinity
// NOTE: 31 bits is not possible due to the idx entry in the Watch struct
const long long INFLPINT = 4e15 + 1;  // 4e15 < 52 bits, based on max long long range captured by double

const int limit32bit = 29;
const int limit32 = 1e9;  // 2^29-2^30
const int limit64bit = 60;
const long long limit64 = 2e18;  // 2^60-2^61
const int limit96bit = 92;
const double limit96 = 8e27;  // 2^92-2^93
const int limit128bit = 124;
const double limit128 = 32e36;  // 2^124-2^125
const int limit256bit = 252;
const double limit256 = 1e76;  // 2^252-2^253

const int conflLimit32 = limit32bit / 2;
const int conflLimit64 = limit64bit / 2;
const int conflLimit96 = limit96bit / 2;
const int conflLimit128 = limit128bit / 2;

template <typename T>
bool fits([[maybe_unused]] const bigint& x) {
  return false;
}
template <>
inline bool fits<int>(const bigint& x) {
  return aux::abs(x) <= bigint(limit32);
}
template <>
inline bool fits<long long>(const bigint& x) {
  return aux::abs(x) <= bigint(limit64);
}
template <>
inline bool fits<int128>(const bigint& x) {
  return aux::abs(x) <= bigint(limit128);
}
template <>
inline bool fits<int256>(const bigint& x) {
  return aux::abs(x) <= bigint(limit256);
}
template <>
inline bool fits<bigint>([[maybe_unused]] const bigint& x) {
  return true;
}
template <typename T, typename S>
bool fitsIn([[maybe_unused]] const S& x) {
  return fits<T>(bigint(x));
}

template <typename T>
bool stillFits([[maybe_unused]] const T& x) {
  return false;
}
template <>
inline bool stillFits<int>(const int& x) {
  return aux::abs(x) <= limit32;
}
template <>
inline bool stillFits<long long>(const long long& x) {
  return aux::abs(x) <= limit64;
}
template <>
inline bool stillFits<int128>(const int128& x) {
  return aux::abs(x) <= limit128;
}
template <>
inline bool stillFits<int256>(const int256& x) {
  return aux::abs(x) <= int256(limit256);
}
template <>
inline bool stillFits<bigint>([[maybe_unused]] const bigint& x) {
  return true;
}

using ActValV = long double;
const ActValV actLimitV = (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 *
                          (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300;  // ~1e2400 << 2^(2^13)

// NOTE: max number of types is 32, as the type is stored with 5 bits in Constr
enum class Origin {
  UNKNOWN,        // uninitialized
  FORMULA,        // original input formula
  DOMBREAKER,     // dominance breaking
  INVALIDATOR,    // solution-invalidating constraint
  PURE,           // pure unit literal
  COREGUIDED,     // extension constraints from coreguided optimization
  HARDENEDBOUND,  // unit constraint due to upper bound on the objective function
  UPPERBOUND,     // upper bound on the objective function
  LOWERBOUND,     // lower bound on the objective function
  LEARNED,        // learned from regular conflict analysis
  FARKAS,         // LP solver infeasibility witness
  DUAL,           // LP solver feasibility dual constraint
  GOMORY,         // Gomory cut
  PROBING,        // probing unit literal
  DETECTEDAMO,    // detected cardinality constraint
  REDUCED,        // reduced constraint
  EQUALITY,       // equality enforcing constraint
  IMPLICATION,    // binary implication clause
};

inline bool isNonImplied(Origin o) {
  return o == Origin::FORMULA || o == Origin::DOMBREAKER || o == Origin::INVALIDATOR;
}
inline bool isBound(Origin o) { return o == Origin::UPPERBOUND || o == Origin::LOWERBOUND; }
inline bool isExternal(Origin o) { return isBound(o) || o == Origin::COREGUIDED; }
inline bool isInput(Origin o) { return o != Origin::UNKNOWN && o < Origin::LEARNED; }
inline bool isLearned(Origin o) { return o >= Origin::LEARNED; }
inline bool usedInTabu(Origin o) { return isNonImplied(o) || o == Origin::UPPERBOUND; }

template <typename SMALL, typename LARGE>
struct ConstrExp;
using ConstrExp32 = ConstrExp<int, long long>;
using ConstrExp64 = ConstrExp<long long, int128>;
using ConstrExp96 = ConstrExp<int128, int128>;
using ConstrExp128 = ConstrExp<int128, int256>;
using ConstrExpArb = ConstrExp<bigint, bigint>;
struct ConstrExpSuper;

template <typename CE>
struct CePtr;
using Ce32 = CePtr<ConstrExp32>;
using Ce64 = CePtr<ConstrExp64>;
using Ce96 = CePtr<ConstrExp96>;
using Ce128 = CePtr<ConstrExp128>;
using CeArb = CePtr<ConstrExpArb>;
using CeSuper = CePtr<ConstrExpSuper>;
using CeNull = CePtr<ConstrExp32>;

template <typename CF, typename DG>
struct ConstrSimple;
using ConstrSimple32 = ConstrSimple<int, long long>;
using ConstrSimple64 = ConstrSimple<long long, int128>;
using ConstrSimple96 = ConstrSimple<int128, int128>;
using ConstrSimple128 = ConstrSimple<int128, int256>;
using ConstrSimpleArb = ConstrSimple<bigint, bigint>;
struct ConstrSimpleSuper;

struct Constr;
struct Clause;
struct Cardinality;

template <typename CF, typename DG>
struct Counting;
using Counting32 = Counting<int, long long>;
template <typename CF, typename DG>
struct CountingSafe;
using Counting64 = CountingSafe<long long, int128>;
using Counting96 = CountingSafe<int128, int128>;
using Counting128 = CountingSafe<int128, int256>;
using CountingArb = CountingSafe<bigint, bigint>;

template <typename CF, typename DG>
struct Watched;
using Watched32 = Watched<int, long long>;
template <typename CF, typename DG>
struct WatchedSafe;
using Watched64 = WatchedSafe<long long, int128>;
using Watched96 = WatchedSafe<int128, int128>;
using Watched128 = WatchedSafe<int128, int256>;
using WatchedArb = WatchedSafe<bigint, bigint>;

template <typename CF>
struct Term {
  Term() : c(0), l(0) {}
  Term(const CF& x, Lit y) : c(x), l(y) {}
  CF c;
  Lit l;
};

// TODO: typedefs for Term, e.g. Term32

template <typename CF>
std::ostream& operator<<(std::ostream& o, const Term<CF>& t) {
  return o << t.c << "x" << t.l;
}

template <typename CF>
std::ostream& operator<<(std::ostream& o, const std::pair<CF, Lit>& cl) {
  return o << (cl.first < 0 ? "" : "+") << cl.first << (cl.second < 0 ? " ~x" : " x") << toVar(cl.second);
}

inline class AsynchronousInterrupt : public std::exception {
 public:
  [[nodiscard]] const char* what() const throw() override { return "Program interrupted by user."; }
} asynchInterrupt;

using TabuRank = long long;

}  // namespace rs
