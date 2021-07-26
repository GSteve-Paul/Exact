/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#include "Implications.hpp"
#include "Solver.hpp"
#include "globals.hpp"

namespace rs {

void Implications::setNbVars(int nvars) { implieds.resize(nvars, {}); }

void Implications::addImplied(Lit a, Lit b) {
  assert(a != b);
  implInMem += implieds[a].insert(b).second;
  resetPropagation();
}

void Implications::removeImplied(Lit a) {
  auto& el = implieds[a];
  implInMem -= el.size();
  el.clear();
}

long long Implications::nImpliedsInMemory() const { return implInMem; }

State Implications::propagate() {
  for (; nextTrailPos < (int)solver.trail.size(); ++nextTrailPos) {
    Lit a = solver.trail[nextTrailPos];
    assert(isTrue(solver.getLevel(), a));
    bool added = false;
    for (Lit b : implieds[a]) {
      if (!isTrue(solver.getLevel(), b)) {
        ++stats.NPROBINGIMPLS;
        ID id = logger ? logger->logRUP(-a, b) : ID_Undef;
        if (solver.learnClause({-a, b}, Origin::IMPLICATION, id) == ID_Unsat) return State::UNSAT;
        added = true;
      }
    }
    if (added) return State::FAIL;
  }
  return State::SUCCESS;
}

}  // namespace rs
