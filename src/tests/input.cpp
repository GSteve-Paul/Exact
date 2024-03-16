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
#include "IntProg.hpp"

using namespace xct;

TEST_SUITE_BEGIN("IntProg input constraints");

TEST_CASE("multiplication simple") {
  Options opts;
  IntProg intprog(opts);
  std::vector<IntVar*> vars;
  vars.reserve(5);
  vars.push_back(intprog.addVar("a", 0, 2, Encoding::LOG));
  vars.push_back(intprog.addVar("b", 0, 2, Encoding::LOG));
  IntVar* rhs = intprog.addVar("z", -10, 10, Encoding::LOG);

  intprog.addMultiplication(vars, rhs, rhs);

  auto [state, cnt] = intprog.count(vars, true);
  CHECK(state == SolveState::SAT);
  CHECK(cnt == 9);
  auto propres = intprog.propagate({rhs}, true);
  CHECK(propres.state == SolveState::SAT);
  CHECK(propres.val == std::vector<std::pair<bigint, bigint>>{{0, 4}});
}

TEST_CASE("multiplication") {
  Options opts;
  IntProg intprog(opts, true);
  std::vector<IntVar*> vars;
  vars.reserve(5);
  vars.push_back(intprog.addVar("a", -3, 4, Encoding::LOG));
  vars.push_back(intprog.addVar("b", -2, 5, Encoding::ORDER));
  vars.push_back(intprog.addVar("c", -1, 6, Encoding::ONEHOT));
  vars.push_back(intprog.addVar("d", 0, 1, Encoding::ORDER));
  vars.push_back(intprog.addVar("e", 2, 2, Encoding::ONEHOT));

  IntVar* z = intprog.addVar("z", -1000, 1000, Encoding::LOG);

  intprog.addMultiplication(vars, z, z);

  auto [state, cnt] = intprog.count(vars, true);
  CHECK(state == SolveState::SAT);
  CHECK(cnt == 1024);
  auto propres = intprog.propagate({z}, true);
  CHECK(propres.state == SolveState::SAT);
  CHECK(propres.val == std::vector<std::pair<bigint, bigint>>{{-180, 240}});

  std::stringstream ss;
  intprog.printInput(ss);
  CHECK(ss.str() == "OBJ MIN \nz[-1000,1000] =< 1*a[-3,4]*b[-2,5]*c[-1,6]*d[0,1]*e[2,2] =< z[-1000,1000]\n");

  // Auxiliary variables are only created when needed
  int64_t internal_nvars = intprog.getSolver().getNbVars();
  intprog.addMultiplication(vars, z, z);
  CHECK(intprog.getSolver().getNbVars() == internal_nvars);
}

TEST_CASE("multiplication edge cases") {
  Options opts;
  IntProg intprog(opts);

  IntVar* a = intprog.addVar("a", -2, 2, Encoding::ONEHOT);
  IntVar* y = intprog.addVar("y", -10, 10, Encoding::LOG);
  IntVar* z = intprog.addVar("z", -10, 10, Encoding::ORDER);
  IntVar* q = intprog.addVar("q", -10, 10, Encoding::LOG);
  IntVar* r = intprog.addVar("r", -10, 10, Encoding::ORDER);

  intprog.addMultiplication({}, q, r);
  intprog.addMultiplication({a}, y, z);

  auto propres = intprog.propagate({a, q, r, y, z}, true);
  CHECK(propres.state == SolveState::SAT);
  CHECK(propres.val == std::vector<std::pair<bigint, bigint>>{{-2, 2}, {-10, 1}, {1, 10}, {-10, 2}, {-2, 10}});
}

TEST_SUITE_END();
