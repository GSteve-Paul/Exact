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
    auto [state, obj] = ilp.toOptimum(ilp.getObjective(), true, 0);
    CHECK(state == SolveState::INCONSISTENT);
    CHECK(obj == 4);
    ilp.setAssumption(vars[4], true);
    auto [state2, obj2] = ilp.toOptimum(ilp.getObjective(), false, 0);
    CHECK(state2 == SolveState::INCONSISTENT);
    CHECK(obj2 == 6);
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
    vars.reserve(5);
    for (const auto& s : {"a", "b", "c", "d", "e", "x"}) {
      vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
    }
    ilp.addConstraint(IntConstraint{{1, 2, 3, 4, 5, 10}, vars, {}, 6});
    ilp.setObjective({1, 1, 2, 3, 5, -10}, vars, {});
    ilp.setAssumption(vars.back(), 0);
    auto [state, obj] = ilp.toOptimum(ilp.getObjective(), true, 0);
    CHECK(state == SolveState::INCONSISTENT);
    CHECK(obj == 4);
    ilp.setAssumption(vars[4], true);
    auto [state2, obj2] = ilp.toOptimum(ilp.getObjective(), true, 0);
    CHECK(state2 == SolveState::INCONSISTENT);
    CHECK(obj2 == 6);
    ilp.setObjective({-1, -1, -1, -1, -1, -1}, vars, {});
    auto [state3, obj3] = ilp.toOptimum(ilp.getObjective(), true, 0);
    CHECK(obj3 == -5);
    ilp.clearAssumptions();
    auto [state4, obj4] = ilp.toOptimum(ilp.getObjective(), true, 0);
    CHECK(obj4 == -6);
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

/*
declare a,b,c,d,e: -> {0..1}.
declare k,l,m,n,o: -> {-1..2}.

1*a()-2*b()+3*c()-1*d()+2*e()-3*k()+1*l()-2*m()+3*n()+3*o() >= 8.

minimize 3*a()-4*b()+1*c()-2*d()+3*e()-4*k()+1*l()-2*m()+3*n()+3*o().
*/
