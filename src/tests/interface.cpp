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

TEST_CASE("toOptimum") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(5);
    for (const auto& s : {"a", "b", "c", "d", "e"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5}, vars, {}, 6});
    ilp.setObjective({1, 1, 2, 3, 5}, vars, {});
    auto [state, obj, optcore1] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state == SolveState::SAT);
    CHECK(obj == 4);
    CHECK(optcore1.empty());
    ilp.setAssumption(vars[4], true);
    auto [state2, obj2, optcore2] = ilp.toOptimum(ilp.getObjective(), false, {false, 0});
    CHECK(state2 == SolveState::SAT);
    CHECK(obj2 == 6);
    CHECK(optcore2.size() == 1);
    CHECK(optcore2[0] == vars[4]);
    ilp.fix(vars[4], 1);
    ilp.addConstraint(IntConstraint{{1, 1, 2, 3, 5}, vars, {}, std::nullopt, 5});
    state = ilp.getOptim()->runFull(false, 0);
    CHECK(state == SolveState::UNSAT);
  }
}

TEST_CASE("toOptimum advanced") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(6);
    for (const auto& s : {"a", "b", "c", "d", "e", "x"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5, 10}, vars, {}, 6});

    ilp.setAssumption(vars[5], false);
    auto [state0, obj0, optcore0] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state0 == SolveState::SAT);
    CHECK(obj0 == 0);
    CHECK(optcore0.empty());

    ilp.setObjective({1, 1, 2, 3, 5, -10}, vars, {});
    auto [state1, obj1, optcore1] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state1 == SolveState::SAT);
    CHECK(obj1 == 4);
    CHECK(optcore1.size() == 1);
    CHECK(optcore1[0] == vars.back());

    ilp.setAssumption(vars[4], true);
    auto [state2, obj2, optcore2] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state2 == SolveState::SAT);
    CHECK(obj2 == 6);
    CHECK(optcore2.size() == 2);

    ilp.setObjective({-1, -1, -1, -1, -1, -1}, vars, {});
    auto [state3, obj3, optcore3] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state3 == SolveState::SAT);
    CHECK(obj3 == -5);
    CHECK(optcore3.size() == 1);
    CHECK(optcore3[0] == vars.back());

    ilp.clearAssumptions();
    auto [state4, obj4, optcore4] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state4 == SolveState::SAT);
    CHECK(obj4 == -6);
    CHECK(optcore4.empty());

    auto [state5, obj5, optcore5] = ilp.toOptimum(ilp.getObjective(), true, {true, 0.0000001});
    CHECK(state5 == SolveState::TIMEOUT);
    CHECK(obj5 == 0);
    CHECK(optcore5.empty());

    for (int64_t i = 2; i < 6; ++i) {
      ilp.setAssumption(vars[i], true);
    }
    for (int64_t i = 2; i < 6; ++i) {
      ilp.setAssumption(vars[i], false);
    }
    auto [state6, obj6, optcore6] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state6 == SolveState::INCONSISTENT);
    CHECK(obj6 == 0);
    CHECK(optcore6.size() == 4);

    ilp.clearAssumption(vars[2]);
    ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5, 10}, vars, {}, std::nullopt, 5});
    auto [state7, obj7, optcore7] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
    CHECK(state7 == SolveState::UNSAT);
    CHECK(obj7 == 0);
    CHECK(optcore7.empty());
  }
}

TEST_CASE("count") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(5);
    for (const auto& s : {"a", "b", "c", "d", "e"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5}, vars, {}, 6});
    ilp.setObjective({1, 1, 2, 3, 5}, vars, {});
    CHECK(ilp.count(vars, true).second == 2);
    CHECK(ilp.count(vars, false).second == 2);
    CHECK(ilp.count(vars, false).second == 0);
  }
}

TEST_CASE("intersect") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(5);
    for (const auto& s : {"a", "b", "c", "d", "e"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    ilp.addConstraint(IntConstraint{{2, 3, 4, 6, 6}, vars, {}, std::nullopt, 10});
    ilp.setObjective({-1, -4, -3, -5, -5}, vars, {});
    auto [solvestate, invalidator] = ilp.getSolIntersection(vars, true);
    CHECK((std::stringstream() << invalidator).str() == "+1 x1 +1 ~x2 +1 x3 >= 1 ;");
    auto [solvestate2, invalidator2] = ilp.getSolIntersection(vars, false);
    CHECK((std::stringstream() << invalidator2).str() == "+1 x1 +1 ~x2 +1 x3 >= 1 ;");
    auto [solvestate3, invalidator3] = ilp.getSolIntersection(vars, false);
    CHECK(invalidator3 == nullptr);
  }
}

TEST_CASE("propagate") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(10);
    for (const auto& s : {"a", "b", "c", "d", "e"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    for (const auto& s : {"k", "l", "m", "n", "o"}) {
      vars.push_back(ilp.addVar(s, -1, 2, Encoding::LOG));
    }
    ilp.addConstraint(IntConstraint{{1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars, {}, 7});
    ilp.setObjective({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars, {});
    auto propres = ilp.propagate(vars, true);
    CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                         {0, 0}, {1, 1}, {1, 1}, {1, 1}, {0, 0}, {2, 2}, {-1, 2}, {-1, 0}, {1, 2}, {1, 2}});
    propres = ilp.propagate(vars, false);
    CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                         {0, 0}, {1, 1}, {1, 1}, {1, 1}, {0, 0}, {2, 2}, {-1, 2}, {-1, 0}, {1, 2}, {1, 2}});
    propres = ilp.propagate(vars, true);
    CHECK(propres == std::vector<std::pair<bigint, bigint>>{});
  }
}

TEST_CASE("pruneDomains") {
  Options opts;
  for (double x : {0.0, 0.5, 1.0}) {
    opts.cgHybrid.set(x);
    ILP ilp(opts);
    std::vector<IntVar*> vars;
    vars.reserve(10);
    for (const auto& s : {"a", "b", "c", "d", "e"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    for (const auto& s : {"k", "l", "m", "n", "o"}) {
      vars.push_back(ilp.addVar(s, -1, 2, Encoding::ONEHOT));
    }
    ilp.addConstraint(IntConstraint{{1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars, {}, 7});
    ilp.setObjective({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars, {});
    auto propres = ilp.pruneDomains(vars, true);
    CHECK(propres ==
          std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {1, 2}});
    propres = ilp.pruneDomains(vars, false);
    CHECK(propres ==
          std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {1, 2}});
    propres = ilp.pruneDomains(vars, true);
    CHECK(propres == std::vector<std::vector<bigint>>{{}, {}, {}, {}, {}, {}, {}, {}, {}, {}});
  }
}

TEST_SUITE_END();
