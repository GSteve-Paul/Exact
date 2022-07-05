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

#include "ConstrExpPools.hpp"
#include "ConstrExp.hpp"

namespace xct {

ConstrExpPools::ConstrExpPools(Options& o) : ce32s(o), ce64s(o), ce96s(o), ce128s(o), ceArbs(o) {}

void ConstrExpPools::resize(size_t newn) {
  ce32s.resize(newn);
  ce64s.resize(newn);
  ce96s.resize(newn);
  ce128s.resize(newn);
  ceArbs.resize(newn);
}

void ConstrExpPools::initializeLogging(std::shared_ptr<Logger> lgr) {
  ce32s.initializeLogging(lgr);
  ce64s.initializeLogging(lgr);
  ce96s.initializeLogging(lgr);
  ce128s.initializeLogging(lgr);
  ceArbs.initializeLogging(lgr);
}

template <>
Ce32 ConstrExpPools::take<int, long long>() {
  return ce32s.take();
}
template <>
Ce64 ConstrExpPools::take<long long, int128>() {
  return ce64s.take();
}
template <>
Ce96 ConstrExpPools::take<int128, int128>() {
  return ce96s.take();
}
template <>
Ce128 ConstrExpPools::take<int128, int256>() {
  return ce128s.take();
}
template <>
CeArb ConstrExpPools::take<bigint, bigint>() {
  return ceArbs.take();
}

Ce32 ConstrExpPools::take32() { return take<int, long long>(); }
Ce64 ConstrExpPools::take64() { return take<long long, int128>(); }
Ce96 ConstrExpPools::take96() { return take<int128, int128>(); }
Ce128 ConstrExpPools::take128() { return take<int128, int256>(); }
CeArb ConstrExpPools::takeArb() { return take<bigint, bigint>(); }

template <typename SMALL, typename LARGE>
ConstrExpPool<SMALL, LARGE>::~ConstrExpPool() {
  for (ConstrExp<SMALL, LARGE>* ce : ces) delete ce;
}

template <typename SMALL, typename LARGE>
void ConstrExpPool<SMALL, LARGE>::resize(size_t newn) {
  assert(n <= INF);
  n = newn;
  for (ConstrExp<SMALL, LARGE>* ce : ces) ce->resize(n);
}

template <typename SMALL, typename LARGE>
void ConstrExpPool<SMALL, LARGE>::initializeLogging(std::shared_ptr<Logger>& lgr) {
  plogger = lgr;
  for (ConstrExp<SMALL, LARGE>* ce : ces) ce->initializeLogging(lgr);
}

template <typename SMALL, typename LARGE>
CePtr<ConstrExp<SMALL, LARGE>> ConstrExpPool<SMALL, LARGE>::take() {
  assert(ces.size() < 100);  // Sanity check that no large amounts of ConstrExps are created
  if (availables.size() == 0) {
    ces.emplace_back(new ConstrExp<SMALL, LARGE>(*this));
    ces.back()->resize(n);
    ces.back()->initializeLogging(plogger);
    availables.push_back(ces.back());
  }
  ConstrExp<SMALL, LARGE>* result = availables.back();
  availables.pop_back();
  assert(result->isReset());
  assert(result->coefs.size() == n);
  return CePtr<ConstrExp<SMALL, LARGE>>(result);
}

template <typename SMALL, typename LARGE>
void ConstrExpPool<SMALL, LARGE>::release(ConstrExp<SMALL, LARGE>* ce) {
  assert(std::any_of(ces.cbegin(), ces.cend(), [&](ConstrExp<SMALL, LARGE>* i) { return i == ce; }));
  assert(std::none_of(availables.cbegin(), availables.cend(), [&](ConstrExp<SMALL, LARGE>* i) { return i == ce; }));
  ce->reset(false);
  availables.push_back(ce);
}

template class ConstrExpPool<int, long long>;
template class ConstrExpPool<long long, int128>;
template class ConstrExpPool<int128, int128>;
template class ConstrExpPool<int128, int256>;
template class ConstrExpPool<bigint, bigint>;

}  // namespace xct
