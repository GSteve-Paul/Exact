/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include "../datastructures/IntMap.hpp"
#include "../typedefs.hpp"
#include "Propagator.hpp"

namespace xct {

class Solver;

struct Repr {
  Lit l;
  ID id;
  std::vector<Lit> equals;
};

class Equalities : public Propagator {  // a union-find data structure
  IntMap<Repr> canonical;

 public:
  Equalities(Solver& s) : Propagator(s) {}
  void setNbVars(int n);

  const Repr& getRepr(Lit a);  // Find
  void merge(Lit a, Lit b);    // Union

  bool isCanonical(Lit l);
  bool isPartOfEquality(Lit l);

  State propagate();
};

}  // namespace xct
