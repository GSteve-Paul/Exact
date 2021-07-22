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

struct LitID {
  Lit l;
  ID id;
};

class Equalities {  // a union-find data structure
  IntMap<LitID> canonical;

 public:
  LitID getRepr(Lit a);      // Find
  void merge(Lit a, Lit b);  // Union
  void setNbVars(int n);
};

}  // namespace rs
