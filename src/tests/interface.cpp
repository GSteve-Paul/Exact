/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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

#include "../external/doctest/doctest.h"
#include "ILP.hpp"

using namespace xct;

TEST_SUITE_BEGIN("ILP interface tests");

TEST_CASE("simple Expression ostream check") {
  Options opts;
  opts.cgHybrid.set(1);
  ILP ilp(opts);
  std::vector<IntVar*> vars;
  vars.reserve(5);
  for (const auto& s : {"a", "b", "c", "d", "e"}) {
    vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
  }
  ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5}, vars, {}, 6});
  ilp.setObjective({1, 1, 2, 3, 5}, vars, {});
  auto [state, obj] = ilp.toOptimum(false);
  CHECK(state == SolveState::INCONSISTENT);
  CHECK(obj == 4);
  ilp.setAssumption(vars[4], true);
  auto [state2, obj2] = ilp.toOptimum(false);
  CHECK(state2 == SolveState::INCONSISTENT);
  CHECK(obj2 == 6);
}

TEST_SUITE_END();
