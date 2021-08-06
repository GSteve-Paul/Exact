/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include "typedefs.hpp"

namespace xct {

class Solver;

class Propagator {
 protected:
  Solver& solver;
  int nextTrailPos = 0;

 public:
  Propagator(Solver& s) : solver(s) {}

  // NOTE: propagate() may backjump in case two equal literals are propagated to an opposite value at the same decision
  // level, as the clause that would prevent this would otherwise trigger unit propagation
  virtual State propagate() = 0;
  void notifyBackjump();
  void resetPropagation();
};

}  // namespace xct
