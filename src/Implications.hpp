/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include "IntMap.hpp"
#include "Propagator.hpp"

namespace rs {

class Solver;

class Implications : public Propagator {
  IntMap<std::unordered_set<Lit>> implieds;
  long long implInMem = 0;

 public:
  Implications(Solver& s) : Propagator(s) {}
  void setNbVars(int n);

  void addImplied(Lit a, Lit b);
  void removeImplied(Lit a);
  const std::unordered_set<Lit>& getImplieds(Lit a) const;
  long long nImpliedsInMemory() const;

  State propagate();
};

}  // namespace rs
