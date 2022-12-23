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

#include "auxiliary.hpp"

std::ostream& operator<<(std::ostream& o, enum SolveState state) {
  switch (state) {
    case (SolveState::UNSAT):
      o << "UNSAT";
      break;
    case (SolveState::INCONSISTENT):
      o << "INCONSISTENT";
      break;
    case (SolveState::INPROCESSED):
      o << "INPROCESSED";
      break;
    case (SolveState::SAT):
      o << "SAT";
      break;
    default:
      assert(false);
  }
  return o;
}

namespace xct::aux {

bigint commonDenominator(const std::vector<ratio>& ratios) {
  bigint cdenom = 1;
  for (const ratio& r : ratios) {
    cdenom = lcm(cdenom, boost::multiprecision::denominator(r));
  }
  return cdenom;
}

namespace rng {

uint32_t seed = 1;

uint32_t xorshift32() {
  /* Algorithm "xor" from p. 4 of Marsaglia, "Xorshift RNGs" */
  seed ^= seed << 13;
  seed ^= seed >> 17;
  seed ^= seed << 5;
  return seed;
}

}  // namespace rng

int32_t getRand(int32_t min, int32_t max) {
  assert(min < max);
  return (((uint64_t)rng::xorshift32() * (uint64_t)(max - min + 1)) >> 32) + min;
}

uint64_t hash(uint64_t x) {
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  x = x ^ (x >> 31);
  return x;
}

uint64_t hashForString(const std::string& els) {
  uint64_t result = els.size();
  for (const char el : els) {
    result ^= hash(std::hash<char>()(el)) + 0x9e3779b9 + (result << 6) + (result >> 2);
  }
  return result;
}

}  // namespace xct::aux
