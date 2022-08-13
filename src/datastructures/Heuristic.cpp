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

void OrderHeap::resize(int newsize) {
  if (cap >= newsize) return;
  // insert elements in such order that tie breaking remains intact
  std::vector<Var> variables;
  while (!empty()) variables.push_back(removeMax());
  tree.clear();
  while (cap < newsize) cap = cap * resize_factor + 1;
  tree.resize(2 * (cap + 1), -1);
  for (Var x : variables) insert(x);
}

void OrderHeap::recalculate() {  // TODO: more efficient implementation
  // insert elements in such order that tie breaking remains intact
  std::vector<Var> variables;
  while (!empty()) variables.push_back(removeMax());
  tree.clear();
  tree.resize(2 * (cap + 1), -1);
  for (Var x : variables) insert(x);
}

void OrderHeap::percolateUp(Var x) {
  for (int at = x + cap + 1; at > 1; at >>= 1) {
    if (tree[at ^ 1] == -1 || activity[x] > activity[tree[at ^ 1]])
      tree[at >> 1] = x;
    else
      break;
  }
}

bool OrderHeap::empty() const { return tree[1] == -1; }
bool OrderHeap::inHeap(Var x) const { return tree[x + cap + 1] != -1; }

void OrderHeap::insert(Var x) {
  assert(x <= cap);
  if (inHeap(x)) return;
  tree[x + cap + 1] = x;
  percolateUp(x);
}

Var OrderHeap::removeMax() {
  Var x = tree[1];
  assert(x != -1);
  tree[x + cap + 1] = -1;
  for (int at = x + cap + 1; at > 1; at >>= 1) {
    if (tree[at ^ 1] != -1 && (tree[at] == -1 || activity[tree[at ^ 1]] > activity[tree[at]]))
      tree[at >> 1] = tree[at ^ 1];
    else
      tree[at >> 1] = tree[at];
  }
  return x;
}

Heuristic::Heuristic() : heap(activity) {}

int Heuristic::nVars() const { return phase.size(); }

void Heuristic::resize(int nvars) {
  assert(nvars > (int)phase.size());
  int old_n = std::max(1, nVars());
  activity.resize(nvars, v_vsids_inc);
  if (options.varOrder) {
    for (Var v = old_n; v < nvars; ++v) {
      activity[v] = 1 / static_cast<ActValV>(v);
    }
  } else {
    for (Var v = old_n; v < nvars; ++v) {
      activity[v] = v_vsids_inc * (aux::getRand(0, 100) / (float)50);
    }
  }
  heap.resize(nvars);
  phase.resize(nvars);
  for (Var v = old_n; v < nvars; ++v) {
    heap.insert(v);
    phase[v] = -v;
  }
}

void Heuristic::undoOne(Var v, Lit l) {
  phase[v] = l;
  heap.insert(v);
}

void Heuristic::setPhase(Var v, Lit l) { phase[v] = l; }
Lit Heuristic::getPhase(Var v) const { return phase[v]; }

ActValV Heuristic::getActivity(Var v) const {
  assert(v > 0);
  assert(v < nVars());
  return activity[v];
}

void Heuristic::vDecayActivity() { v_vsids_inc *= (1 / options.varDecay.get()); }
void Heuristic::vBumpActivity(Var v) {
  assert(!options.varOrder);
  assert(v > 0);
  if ((activity[v] += v_vsids_inc) > actLimitV) {  // Rescale
    for (Var x = 1; x < nVars(); ++x) {
      activity[x] /= actLimitV;
      activity[x] /= actLimitV;
    }
    v_vsids_inc /= actLimitV;
    v_vsids_inc /= actLimitV;
  }
  // Update heap with respect to new activity:
  if (heap.inHeap(v)) {
    heap.percolateUp(v);
  }
}
void Heuristic::vBumpActivity(const std::vector<Lit>& lits) {
  if (options.varOrder) {
    return;
  }
  for (Lit l : lits) {
    if (l != 0) {
      vBumpActivity(toVar(l));
    }
  }
}

Lit Heuristic::pickBranchLit(const std::vector<int>& position) {
  Var next = 0;
  // Activity based decision:
  while (next == 0 || isKnown(position, next)) {
    if (heap.empty()) {
      return 0;
    } else {
      next = heap.removeMax();
    }
  }
  assert(next != 0);
  return getPhase(next);
}

}  // namespace xct
