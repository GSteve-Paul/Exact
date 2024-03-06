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

TEST_SUITE_BEGIN("ILP inference tests");

constexpr double timeouttime = 0.0000001;

TEST_CASE("toOptimum") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(5);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }

      auto [state, obj, optcore] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state == SolveState::SAT);
      CHECK(obj == 0);
      CHECK(optcore->empty());

      ilp.setObjective(IntConstraint::zip({1, 1, 2, 3, 5}, vars));
      auto [state1, obj1, optcore1] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state1 == SolveState::SAT);
      CHECK(obj1 == 0);
      CHECK(optcore1->empty());

      ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5}, vars), 6});
      auto [state0, obj0, optcore0] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state0 == SolveState::SAT);
      CHECK(obj0 == 4);
      CHECK(optcore0->empty());

      ilp.setAssumption(vars[4], true);
      auto [state2, obj2, optcore2] = ilp.toOptimum(ilp.getObjective(), false, {false, 0});
      CHECK(state2 == SolveState::SAT);
      CHECK(obj2 == 6);
      CHECK(optcore2->size() == 1);
      CHECK(optcore2->contains(vars[4]));
      ilp.fix(vars[4], 1);
      ilp.addConstraint({IntConstraint::zip({1, 1, 2, 3, 5}, vars), std::nullopt, 5});
      state = ilp.getOptim()->runFull(false, 0);
      CHECK(state == SolveState::UNSAT);
    }
  }
}

TEST_CASE("toOptimum advanced") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(6);
      for (const auto& s : {"a", "b", "c", "d", "e", "x"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }

      ilp.setAssumption(vars[5], false);
      auto [state, obj, optcore] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state == SolveState::SAT);
      CHECK(obj == 0);
      CHECK(optcore->empty());

      ilp.setObjective(IntConstraint::zip({1, 1, 2, 3, 5, -10}, vars));
      auto [state0, obj0, optcore0] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state0 == SolveState::SAT);
      CHECK(obj0 == 0);
      CHECK(optcore0->size() == 1);
      CHECK(optcore0->contains(vars[5]));

      ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5, 10}, vars), 6});
      auto [state1, obj1, optcore1] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state1 == SolveState::SAT);
      CHECK(obj1 == 4);
      CHECK(optcore1->size() == 1);
      CHECK(optcore1->contains(vars[5]));

      ilp.setAssumption(vars[4], true);
      auto [state2, obj2, optcore2] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state2 == SolveState::SAT);
      CHECK(obj2 == 6);
      CHECK(optcore2->size() == 2);
      CHECK(optcore2->contains(vars[5]));
      CHECK(optcore2->contains(vars[4]));

      ilp.setObjective(IntConstraint::zip({-1, -1, -1, -1, -1, -1}, vars));
      auto [state3, obj3, optcore3] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state3 == SolveState::SAT);
      CHECK(obj3 == -5);
      CHECK(optcore3->size() == 1);
      CHECK(optcore3->contains(vars[5]));

      ilp.clearAssumptions();
      auto [state4, obj4, optcore4] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state4 == SolveState::SAT);
      CHECK(obj4 == -6);
      CHECK(optcore4->empty());

      auto [state5, obj5, optcore5] = ilp.toOptimum(ilp.getObjective(), true, {true, timeouttime});
      CHECK(state5 == SolveState::TIMEOUT);
      CHECK(obj5 == 0);
      CHECK(optcore5->empty());

      for (int64_t i = 2; i < 6; ++i) {
        ilp.setAssumption(vars[i], true);
      }
      for (int64_t i = 2; i < 6; ++i) {
        ilp.setAssumption(vars[i], false);
      }
      auto [state6, obj6, optcore6] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state6 == SolveState::INCONSISTENT);
      CHECK(obj6 == 0);
      CHECK(optcore6->size() == 4);

      ilp.clearAssumption(vars[2]);
      ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5, 10}, vars), std::nullopt, 5});
      auto [state7, obj7, optcore7] = ilp.toOptimum(ilp.getObjective(), true, {false, 0});
      CHECK(state7 == SolveState::UNSAT);
      CHECK(obj7 == 0);
      CHECK(optcore7->empty());
    }
  }
}

TEST_CASE("count") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);

      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(5);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }

      CHECK(ilp.count(vars, true).second == 32);

      ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5}, vars), 6});
      CHECK(ilp.count(vars, true).second == 22);

      ilp.setObjective(IntConstraint::zip({1, 1, 2, 3, 5}, vars));

      CHECK(ilp.count(vars, true).second == 2);
      CHECK(ilp.count(vars, false).second == 2);
      CHECK(ilp.count(vars, false).second == 0);
    }
  }
}

TEST_CASE("count advanced") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (int i = 0; i < 2; ++i) {
      opts.optCoreguided.set(ii);
      for (double x : {0.0, 0.5, 1.0}) {
        opts.optRatio.set(x);
        ILP ilp(opts);
        std::vector<IntVar*> vars;
        vars.reserve(5);
        for (const auto& s : {"a", "b", "c", "d", "e"}) {
          vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
        }

        ilp.setAssumption(vars[4], false);
        auto [state0, count0] = ilp.count(vars, true);
        CHECK(state0 == SolveState::SAT);
        CHECK(count0 == 16);

        ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5}, vars), 6});
        auto [state1, count1] = ilp.count(vars, true);
        CHECK(state1 == SolveState::SAT);
        CHECK(count1 == 7);

        ilp.setObjective(IntConstraint::zip({1, 1, 2, 3, 5}, vars));
        auto [state2, count2] = ilp.count(vars, true);
        CHECK(state2 == SolveState::SAT);
        CHECK(count2 == 2);

        ilp.setObjective(IntConstraint::zip({-1, -1, -2, -3, -5}, vars));
        auto [state3, count3] = ilp.count(vars, true, {true, timeouttime});
        CHECK(state3 == SolveState::TIMEOUT);
        CHECK(count3 < 0);

        auto [state4, count4] = ilp.count(vars, true);
        CHECK(state4 == SolveState::SAT);
        CHECK(count4 == 1);

        ilp.setAssumption(vars[3], false);
        ilp.setAssumption(vars[1], false);
        auto [state5, count5] = ilp.count(vars, true);
        CHECK(state5 == SolveState::INCONSISTENT);
        CHECK(count5 == 0);

        ilp.clearAssumptions();
        ilp.addConstraint({IntConstraint::zip({1, 2, 3, 4, 5}, vars), std::nullopt, 5});
        auto [state6, count6] = ilp.count(vars, true);
        CHECK(state6 == SolveState::UNSAT);
        CHECK(count6 == 0);
      }
    }
  }
}

TEST_CASE("intersect") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(5);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }

      auto [solvestate, invalidator] = ilp.getSolIntersection(vars, true);
      CHECK((std::stringstream() << invalidator).str() == ">= 1 ;");

      ilp.setObjective(IntConstraint::zip({-1, -4, -3, -5, -5}, vars));
      auto [solvestate0, invalidator0] = ilp.getSolIntersection(vars, true);
      CHECK((std::stringstream() << invalidator0).str() == "+1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 +1 ~x5 >= 1 ;");

      ilp.addConstraint({IntConstraint::zip({2, 3, 4, 6, 6}, vars), std::nullopt, 10});
      auto [solvestate1, invalidator1] = ilp.getSolIntersection(vars, true);
      CHECK((std::stringstream() << invalidator1).str() == "+1 x1 +1 ~x2 +1 x3 >= 1 ;");

      SolveState res = ilp.getOptim()->runFull(false, 0);
      CHECK(res == SolveState::SAT);

      auto [solvestate2, invalidator2] = ilp.getSolIntersection(vars, false);
      CHECK((std::stringstream() << invalidator2).str() == "+1 x1 +1 ~x2 +1 x3 >= 1 ;");

      auto [solvestate3, invalidator3] = ilp.getSolIntersection(vars, false);
      CHECK(invalidator3 == nullptr);
    }
  }
}

TEST_CASE("intersect advanced") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(5);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      ilp.setAssumption(vars[0], false);
      auto [state0, invalidator0] = ilp.getSolIntersection(vars, true);
      CHECK(state0 == SolveState::SAT);
      CHECK((std::stringstream() << invalidator0).str() == "+1 x1 >= 1 ;");

      ilp.addConstraint({IntConstraint::zip({2, 3, 4, 6, 6}, vars), std::nullopt, 10});
      auto [state1, invalidator1] = ilp.getSolIntersection(vars, true);
      CHECK(state1 == SolveState::SAT);
      CHECK((std::stringstream() << invalidator1).str() == "+1 x1 >= 1 ;");

      ilp.setObjective(IntConstraint::zip({-1, -4, -3, -5, -5}, vars));
      auto [state2, invalidator2] = ilp.getSolIntersection(vars, true);
      CHECK(state2 == SolveState::SAT);
      CHECK((std::stringstream() << invalidator2).str() == "+1 x1 +1 ~x2 +1 x3 >= 1 ;");

      auto [state3, invalidator3] = ilp.getSolIntersection(vars, true, {true, timeouttime});
      CHECK(state3 == SolveState::TIMEOUT);
      CHECK(invalidator3 == nullptr);

      std::vector<IntVar*> vars2 = vars;
      vars2.resize(2);
      auto [state4, invalidator4] = ilp.getSolIntersection(vars2, true);
      CHECK(state4 == SolveState::SAT);
      CHECK((std::stringstream() << invalidator4).str() == "+1 x1 +1 ~x2 >= 1 ;");

      ilp.setAssumption(vars[3], true);
      ilp.setAssumption(vars[4], true);
      auto [state5, invalidator5] = ilp.getSolIntersection(vars2, true);
      CHECK(state5 == SolveState::INCONSISTENT);
      CHECK(invalidator5 == nullptr);

      ilp.clearAssumption(vars[4]);
      ilp.clearAssumption(vars[3]);
      ilp.fix(vars[4], 1);
      ilp.fix(vars[3], 1);
      auto [state6, invalidator6] = ilp.getSolIntersection(vars2, true);
      CHECK(state6 == SolveState::UNSAT);
      CHECK(invalidator6 == nullptr);
    }
  }
}

TEST_CASE("propagate") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(10);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      for (const auto& s : {"k", "l"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::ORDER));
      }
      for (const auto& s : {"m", "n"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::LOG));
      }
      vars.push_back(ilp.addVar("o", -1, 2, Encoding::ONEHOT));

      auto propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {-1, 2}, {-1, 2}, {-1, 2}, {-1, 2}, {-1, 2}});

      ilp.addConstraint({IntConstraint::zip({1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars), 7});
      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {-1, 2}, {-1, 2}, {-1, 2}, {-1, 2}, {-1, 2}});

      ilp.setObjective(IntConstraint::zip({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars));
      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 0}, {1, 1}, {1, 1}, {1, 1}, {0, 0}, {2, 2}, {-1, 2}, {-1, 0}, {1, 2}, {1, 2}});

      propres = ilp.propagate(vars, false);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 0}, {1, 1}, {1, 1}, {1, 1}, {0, 0}, {2, 2}, {-1, 2}, {-1, 0}, {1, 2}, {1, 2}});

      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{});
    }
  }
}

TEST_CASE("propagate advanced") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(10);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      for (const auto& s : {"k", "l"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::ORDER));
      }
      for (const auto& s : {"m", "n"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::LOG));
      }
      vars.push_back(ilp.addVar("o", -1, 2, Encoding::ONEHOT));

      ilp.setAssumption(vars[7], std::vector<bigint>{1});
      auto propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {-1, 2}, {-1, 2}, {1, 1}, {-1, 2}, {-1, 2}});

      ilp.addConstraint({IntConstraint::zip({1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars), 7});
      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {-1, 2}, {-1, 2}, {1, 1}, {-1, 2}, {-1, 2}});

      ilp.setObjective(IntConstraint::zip({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars));
      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 0}, {1, 1}, {1, 1}, {0, 1}, {0, 1}, {1, 2}, {0, 2}, {1, 1}, {2, 2}, {2, 2}});

      propres = ilp.propagate(vars, false);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{
                           {0, 0}, {1, 1}, {1, 1}, {0, 1}, {0, 1}, {1, 2}, {0, 2}, {1, 1}, {2, 2}, {2, 2}});

      propres = ilp.propagate(vars, true);
      CHECK(propres == std::vector<std::pair<bigint, bigint>>{});
    }
  }
}

TEST_CASE("pruneDomains") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(10);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      for (const auto& s : {"k", "l", "m", "n", "o"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::ONEHOT));
      }

      auto propres = ilp.pruneDomains(vars, true);
      CHECK(propres == std::vector<std::vector<bigint>>{{0, 1},
                                                        {0, 1},
                                                        {0, 1},
                                                        {0, 1},
                                                        {0, 1},
                                                        {-1, 0, 1, 2},
                                                        {-1, 0, 1, 2},
                                                        {-1, 0, 1, 2},
                                                        {-1, 0, 1, 2},
                                                        {-1, 0, 1, 2}});

      ilp.setObjective(IntConstraint::zip({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars));
      propres = ilp.pruneDomains(vars, true);
      CHECK(propres == std::vector<std::vector<bigint>>{{0}, {1}, {0}, {1}, {0}, {2}, {-1}, {2}, {-1}, {-1}});

      ilp.addConstraint({IntConstraint::zip({1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars), 7});
      propres = ilp.pruneDomains(vars, true);
      CHECK(propres ==
            std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {1, 2}});

      propres = ilp.pruneDomains(vars, true);
      CHECK(propres ==
            std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {1, 2}});

      propres = ilp.pruneDomains(vars, false);
      CHECK(propres ==
            std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {1, 2}});

      propres = ilp.pruneDomains(vars, true);
      CHECK(propres == std::vector<std::vector<bigint>>{{}, {}, {}, {}, {}, {}, {}, {}, {}, {}});
    }
  }
}

TEST_CASE("pruneDomains advanced") {
  Options opts;
  for (int ii = 0; ii < 2; ++ii) {
    opts.optCoreguided.set(ii);
    for (double x : {0.0, 0.5, 1.0}) {
      opts.optRatio.set(x);
      ILP ilp(opts);
      std::vector<IntVar*> vars;
      vars.reserve(10);
      for (const auto& s : {"a", "b", "c", "d", "e"}) {
        vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
      }
      for (const auto& s : {"k", "l", "m", "n", "o"}) {
        vars.push_back(ilp.addVar(s, -1, 2, Encoding::ONEHOT));
      }

      ilp.setAssumption(vars[9], std::vector<bigint>{0});
      auto propres = ilp.pruneDomains(vars, true);
      CHECK(
          propres ==
          std::vector<std::vector<bigint>>{
              {0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}, {-1, 0, 1, 2}, {-1, 0, 1, 2}, {-1, 0, 1, 2}, {-1, 0, 1, 2}, {0}});

      ilp.setObjective(IntConstraint::zip({3, -4, 1, -2, 3, -4, 1, -2, 3, 3}, vars));
      propres = ilp.pruneDomains(vars, true);
      CHECK(propres == std::vector<std::vector<bigint>>{{0}, {1}, {0}, {1}, {0}, {2}, {-1}, {2}, {-1}, {0}});

      ilp.addConstraint({IntConstraint::zip({1, -2, 3, -1, 2, -3, 1, -2, 3, 3}, vars), 7});
      propres = ilp.pruneDomains(vars, true);
      CHECK(propres == std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {1}, {2}, {-1}, {2}, {0}});

      ilp.setAssumption(vars[9], std::vector<bigint>{0, 2});
      propres = ilp.pruneDomains(vars, true);
      CHECK(propres ==
            std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {2}, {-1, 1, 2}, {-1, 0}, {1, 2}, {2}});

      ilp.setAssumption(vars[8], std::vector<bigint>{-1, 0});
      propres = ilp.pruneDomains(vars, false);
      CHECK(propres == std::vector<std::vector<bigint>>{{0}, {1}, {1}, {1}, {0}, {1}, {2}, {-1}, {0}, {2}});
    }
  }
}

TEST_CASE("extract MUS") {
  Options opts;
  opts.lpTimeRatio.set(0);
  opts.inpProbing.set(0);
  opts.inpAMO.set(0);
  ILP ilp(opts);
  std::vector<IntVar*> vars;
  vars.reserve(10);
  for (const auto& s : {"a", "b", "c", "d", "e", "f"}) {
    vars.push_back(ilp.addVar(s, 0, 1, Encoding::ORDER));
  }
  vars.push_back(ilp.addVar("x", -2, 2, Encoding::ORDER));
  vars.push_back(ilp.addVar("y", -2, 2, Encoding::ONEHOT));
  vars.push_back(ilp.addVar("z", -2, 2, Encoding::LOG));

  std::vector<IntVar*> abc = {vars[0], vars[1], vars[2]};
  std::vector<IntVar*> defxyz = {vars[3], vars[4], vars[5], vars[6], vars[7], vars[8]};

  ilp.addConstraint({IntConstraint::zip({1, 1, 1, 1, 1, 1}, defxyz), -5});
  ilp.addConstraint({{{1, vars[0]}, {1, vars[1]}, {1, vars[3]}}, 1});
  ilp.addConstraint({{{1, vars[1]}, {1, vars[2]}, {1, vars[4]}}, 1});
  ilp.addConstraint({{{1, vars[2]}, {1, vars[0]}, {1, vars[5]}}, 1});
  ilp.addConstraint({IntConstraint::zip({-1, -1, -1}, abc), -1});

  Core core = ilp.extractMUS();
  CHECK(!core);

  ilp.setAssumptions({{vars[3], 0}, {vars[4], 0}, {vars[5], 0}, {vars[6], -2}, {vars[7], -2}, {vars[8], -2}});
  SolveState res = ilp.getOptim()->runFull(false, 0);
  CHECK(res == SolveState::INCONSISTENT);

  core = ilp.getLastCore();
  CHECK(core);
  CHECK(core->size() == 6);

  core = ilp.extractMUS();
  CHECK(core);
  CHECK(core->size() == 3);

  core = ilp.extractMUS({true, timeouttime});
  CHECK(!core);

  // check that state has not been altered
  ilp.clearAssumptions();
  CHECK(ilp.count(vars, true).second == 1625);
}

TEST_SUITE_END();
