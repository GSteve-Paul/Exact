/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2024 Jo Devriendt, Nonfiction Software

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

TEST_SUITE_BEGIN("optimization");

TEST_CASE("knapsack") {
  Options opts;
  for (double ratio : {0.0, 0.5, 1.0}) {
    opts.optRatio.set(ratio);
    for (int precision : {2, 10, 50, 100}) {
      opts.optPrecision.set(precision);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(10);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      for (const auto& s : {"k", "l"}) {
        vars.push_back(ilp.addVar(s, -2, 2, Encoding::ORDER));
      }
      for (const auto& s : {"m", "n"}) {
        vars.push_back(ilp.addVar(s, -2, 2, Encoding::LOG));
      }
      vars.push_back(ilp.addVar("o", -2, 2, Encoding::ONEHOT));

      ilp.setObjective(IntConstraint::zip({3, -4, 1, -2, 3, -4, 1, -2, 3, 4}, vars));
      ilp.addConstraint({IntConstraint::zip({1, -2, 3, -1, 2, -3, 1, -2, 3, -3}, vars), 7});
      SolveState res = ilp.getOptim()->runFull(true, 0);

      CHECK(res == SolveState::UNSAT);
      CHECK(ilp.getUpperBound() == -14);
    }
  }
}

TEST_SUITE_END();
