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

#include "SolverStructs.hpp"

namespace rs {

struct OrderHeap {  // segment tree (fast implementation of priority queue).
  std::vector<ActValV>& activity;
  int cap = 0;
  std::vector<Var> tree = {-1, -1};

  explicit OrderHeap(std::vector<ActValV>& a) : activity(a) {}

  void resize(int newsize);
  void recalculate();
  void percolateUp(Var x);
  [[nodiscard]] bool empty() const;
  [[nodiscard]] bool inHeap(Var x) const;
  void insert(Var x);
  Var removeMax();
};

class Heuristic {
 public:
  std::vector<Lit> phase;
  std::vector<ActValV> activity;
  ActValV v_vsids_inc = 1.0;
  OrderHeap heap;

  int nVars() const;

 public:
  Heuristic();
  void resize(int n);

  void undoOne(Var v, Lit l);
  void setPhase(Var v, Lit l);
  Lit getPhase(Var v) const;

  ActValV getActivity(Var v) const;
  void vDecayActivity();
  void vBumpActivity(Var v);
  void vBumpActivity(const std::vector<Lit>& lits);

  Lit pickBranchLit(const std::vector<int>& position);
};

}  // namespace rs