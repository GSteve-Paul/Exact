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

#include "Stats.hpp"

namespace xct {

std::ostream& operator<<(std::ostream& o, const Stat& stat) {
  o << stat.name << " ";
  return aux::prettyPrint(o, stat.z);
}

void operator++(Stat& stat) { stat.z++; }
void operator--(Stat& stat) { stat.z--; }

StatNum operator+(const Stat& x, const Stat& y) { return x.z + y.z; }
StatNum operator-(const Stat& x, const Stat& y) { return x.z - y.z; }
StatNum operator*(const Stat& x, const Stat& y) { return x.z * y.z; }
StatNum operator/(const Stat& x, const Stat& y) { return x.z / y.z; }
bool operator==(const Stat& x, const Stat& y) { return x.z == y.z; }
bool operator>(const Stat& x, const Stat& y) { return x.z > y.z; }
bool operator<(const Stat& x, const Stat& y) { return x.z < y.z; }
bool operator<=(const Stat& x, const Stat& y) { return x.z <= y.z; }
bool operator>=(const Stat& x, const Stat& y) { return x.z >= y.z; }

StatNum Stats::getTime() const {
  return std::chrono::duration_cast<std::chrono::duration<double>>(std::chrono::steady_clock::now() - startTime)
      .count();
}
StatNum Stats::getRunTime() const {
  return std::chrono::duration_cast<std::chrono::duration<double>>(std::chrono::steady_clock::now() - runStartTime)
      .count();
}
StatNum Stats::getSolveTime() const { return SOLVETIMEFREE + SOLVETIMEASSUMP; }
// NOTE: below linear relations were determined by regression tests on experimental data,
// so that the deterministic time correlates as closely as possible with the cpu time in seconds
StatNum Stats::getLpDetTime() const { return (5.92 * NLPOPERATIONS + 1105.48 * NLPADDEDLITERALS) / 1e9; }
StatNum Stats::getNonLpDetTime() const {
  return (49.00 * NWATCHLOOKUPS + 9.09 * NWATCHCHECKS + 3.55 * NPROPCHECKS + 60.69 * NSATURATESTEPS +
          61.86 * (NADDEDLITERALS - NLPADDEDLITERALS) + 1484.40 * NWEAKENEDNONIMPLIED + 268.51 * NTRAILPOPS) /
         1e9;
}

StatNum Stats::getDetTime() const { return getLpDetTime() + getNonLpDetTime(); }

void Stats::print(const StatNum& lowerbound, const StatNum& upperbound) {
  setDerivedStats(lowerbound, upperbound);
  for (Stat* s : statsToDisplay) {
    std::cout << "c " << *s << std::endl;
  }
}

void Stats::printCsvLine(const StatNum& lowerbound, const StatNum& upperbound) {
  setDerivedStats(lowerbound, upperbound);
  std::cout << "c csvline";
  for (Stat* s : statsToDisplay) {
    aux::prettyPrint(std::cout << ",", s->z);
  }
  std::cout << std::endl;
}

void Stats::printCsvHeader() {
  setDerivedStats(std::numeric_limits<StatNum>::quiet_NaN(), std::numeric_limits<StatNum>::quiet_NaN());
  std::cout << "c csvheader";
  for (Stat* s : statsToDisplay) {
    std::cout << "," << s->name;
  }
  std::cout << std::endl;
}

}  // namespace xct
