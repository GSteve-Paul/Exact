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

#include <ostream>
#include "../typedefs.hpp"
#include "IntMap.hpp"

namespace xct {

struct CRef {
  uint32_t ofs = std::numeric_limits<uint32_t>::max();
  bool operator==(CRef const& o) const { return ofs == o.ofs; }
  bool operator!=(CRef const& o) const { return ofs != o.ofs; }
  bool operator<(CRef const& o) const { return ofs < o.ofs; }
};
inline std::ostream& operator<<(std::ostream& o, const CRef& c) { return o << c.ofs; }

const CRef CRef_Undef = {std::numeric_limits<uint32_t>::max()};
const CRef CRef_Unsat = {std::numeric_limits<uint32_t>::max() - 1};
inline bool isValid(CRef cr) { return cr.ofs < std::numeric_limits<uint32_t>::max() - 1; };

// TODO: make below methods part of a Solver object that's passed around
inline bool isTrue(const IntMap<int>& level, Lit l) { return level[l] != INF; }
inline bool isFalse(const IntMap<int>& level, Lit l) { return level[-l] != INF; }
inline bool isUnit(const IntMap<int>& level, Lit l) { return level[l] == 0; }
inline bool isUnknown(const std::vector<int>& pos, Lit l) { return pos[toVar(l)] == INF; }
inline bool isKnown(const std::vector<int>& pos, Lit l) { return pos[toVar(l)] != INF; }
// NOTE: below assumes isKnown(position,l)
inline bool isDecided(const std::vector<CRef>& reasons, Var v) { return reasons[v] == CRef_Undef; }
inline bool isPropagated(const std::vector<CRef>& reasons, Lit l) { return !isDecided(reasons, toVar(l)); }

struct Watch {
  CRef cref;
  int idx;
  /**
   * idx<0: blocked literal for clausal propagation
   * 0<=idx<INF: index of watched literal for cardinality propagation
   * INF<=idx: index of watched literal for watched/counting propagation
   **/
  Watch(CRef cr, int i) : cref(cr), idx(i){};
  bool operator==(const Watch& other) const { return other.cref == cref && other.idx == idx; }
};

// ---------------------------------------------------------------------
// Memory. Maximum supported size of learnt constraint database is 16GB

struct ConstraintAllocator {
  uint32_t* memory = nullptr;  // TODO: why not uint64_t?
  uint32_t at = 0, cap = 0;
  uint32_t wasted = 0;  // for GC
  void capacity(uint32_t min_cap);
  template <typename C>
  C* alloc(int nTerms) {
    uint32_t oldAt = at;
    at += C::getMemSize(nTerms);
    capacity(at);
    return (C*)(memory + oldAt);
  }
  Constr& operator[](CRef cr) const { return (Constr&)*(memory + cr.ofs); }
};

class OutOfMemoryException : public std::exception {};
static inline void* xrealloc(void* ptr, size_t size) {
  void* mem = realloc(ptr, size);
  if (mem == nullptr && errno == ENOMEM)
    throw OutOfMemoryException();
  else
    return mem;
}

}  // namespace xct

namespace std {
template <>
struct hash<xct::CRef> {
  size_t operator()(xct::CRef const& cr) const noexcept { return cr.ofs; }
};
}  // namespace std