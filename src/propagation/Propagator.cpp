/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "Propagator.hpp"
#include "../Solver.hpp"

namespace xct {

void Propagator::notifyBackjump() {
  nextTrailPos =
      std::min(nextTrailPos, solver.decisionLevel() == 0 ? (int)solver.trail.size() : solver.trail_lim.back());
}

void Propagator::resetPropagation() { nextTrailPos = 0; }

}  // namespace xct
