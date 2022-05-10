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

#include "Heuristic.hpp"
#include "../globals.hpp"

namespace xct {

Heuristic::Heuristic() : nextDecision(0) {
  phase.resize(1);
  phase[0] = 0;
  actList.resize(1);
  actList[0].prev = 0;
  actList[0].next = 0;
  actList[0].activity = std::numeric_limits<ActValV>::max();
}

int Heuristic::nVars() const { return phase.size(); }

void Heuristic::swapOrder(Var v1, Var v2) {
  ActNode tmp1 = actList[v1];
  actList[tmp1.prev].next = v2;
  actList[tmp1.next].prev = v2;
  ActNode tmp2 = actList[v2];
  actList[tmp2.prev].next = v1;
  actList[tmp2.next].prev = v1;
  actList[v1] = tmp2;
  actList[v2] = tmp1;
}

bool Heuristic::before(Var v1, Var v2) const {
  return actList[v1].activity > actList[v2].activity || (actList[v1].activity == actList[v2].activity && v1 < v2);
}

void Heuristic::resize(int nvars) {
  assert(nvars == 1 || nvars > (int)phase.size());
  int old_n = nVars();  // at least one after initialization
  phase.resize(nvars);
  actList.resize(nvars);
  for (Var v = old_n; v < nvars; ++v) {
    phase[v] = -v;
    ActNode& node = actList[v];
    node.activity = -v / static_cast<double>(INF);  // early variables have slightly higher initial activity
    actList[v].next = v + 1;
    actList[v].prev = v - 1;
    assert(before(nextDecision, v));
  }
  Var oldTail = actList[0].prev;
  actList[old_n].prev = oldTail;
  actList[oldTail].next = old_n;
  actList[0].prev = nvars - 1;
  actList[nvars - 1].next = 0;
  if (options.test.get() != 0 || options.randomSeed.get() != 1) {
    for (Var v = old_n; v < nvars; ++v) {
      swapOrder(v, aux::getRand(1, v));  // swap to the front
      if (before(v, nextDecision)) nextDecision = v;
    }
  }
}

void Heuristic::undoOne(Var v, Lit l) {
  phase[v] = l;
  if (before(v, nextDecision)) nextDecision = v;
}

void Heuristic::setPhase(Var v, Lit l) { phase[v] = l; }
Lit Heuristic::getPhase(Var v) const { return phase[v]; }

ActValV Heuristic::getActivity(Var v) const {
  assert(v > 0);
  assert(v < nVars());
  return actList[v].activity;
}

void Heuristic::vBumpActivity(const std::vector<Lit>& lits, const std::vector<int>& position) {
  double weightNew = options.varWeight.get();
  double weightOld = 1 - weightNew;
  ActValV nConfl = stats.NCONFL.z;
  std::vector<Var> vars;
  vars.reserve(lits.size());
  for (Lit l : lits) {
    assert(l != 0);
    Var v = toVar(l);
    actList[v].activity = weightOld * actList[v].activity + weightNew * nConfl;
    vars.push_back(v);
  }
  std::sort(vars.begin(), vars.end(), [&](const Var& v1, const Var& v2) { return before(v1, v2); });
  for (Var v : vars) {
    if (before(nextDecision, v)) {
      break;  // vars is sorted
    } else if (isUnknown(position, v)) {
      nextDecision = v;
      break;  // vars is sorted
    }
  }
  Var current = actList[0].next;
  for (Var v : vars) {
    while (current != 0 && before(current, v)) {
      current = actList[current].next;
    }
    if (current == v) continue;
    // eject v from list
    actList[actList[v].next].prev = actList[v].prev;
    actList[actList[v].prev].next = actList[v].next;
    // insert v before current
    Var before = actList[current].prev;
    actList[v].prev = before;
    actList[v].next = current;
    actList[before].next = v;
    actList[current].prev = v;
  }
}

// NOTE: so far, this is only called when the returned lit will be decided shortly
Lit Heuristic::pickBranchLit(const std::vector<int>& position) {
  assert(testActList(position));
  assert(getPhase(0) == 0);        // so will return right phase
  assert(isUnknown(position, 0));  // so will eventually stop
  // Activity based decision:
  if (nextDecision == 0) {
    nextDecision = actList[0].next;
  }
  while (isKnown(position, nextDecision)) {
    nextDecision = actList[nextDecision].next;
  }
  return getPhase(nextDecision);
}

// NOTE: v==0 will give first in activity order
Var Heuristic::nextInActOrder(Var v) const { return actList[v].next; }

bool Heuristic::testActList(const std::vector<int>& position) const {
  // printActList(position);
  Var current = actList[0].next;
  int tested = 1;
  while (current != 0) {
    ++tested;
    Var next = actList[current].next;
    assert(next == 0 || before(current, next));
    assert(actList[next].prev == current);
    current = next;
  }
  assert(tested == (int)actList.size());
  current = nextDecision == 0 ? 0 : actList[nextDecision].prev;
  while (current != 0) {
    assert(isKnown(position, current));
    current = actList[current].prev;
  }
  return true;
}

void Heuristic::printActList(const std::vector<int>& position) const {
  std::cout << nextDecision << " :: ";
  for (Var v = 0; v < (int)actList.size(); ++v) {
    std::cout << actList[v].prev << "->" << v << "->" << actList[v].next << " " << actList[v].activity << " "
              << isKnown(position, v) << " | ";
  }
  std::cout << std::endl;
}

}  // namespace xct
