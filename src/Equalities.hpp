/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include "IntMap.hpp"
#include "typedefs.hpp"

namespace rs {

class Solver;

struct Repr {
  Lit l;
  ID id;
  std::vector<Lit> equals;
};

class Equalities {  // a union-find data structure
  IntMap<Repr> canonical;
  Solver& solver;

  int nextTrailPos = 0;

 public:
  Equalities(Solver& s) : solver(s) {}
  void setNbVars(int n);

  const Repr& getRepr(Lit a);  // Find
  void merge(Lit a, Lit b);    // Union
  bool isCanonical(Lit l);

  State propagate();
  void notifyBackjump(int newTrailSize);
};

}  // namespace rs
