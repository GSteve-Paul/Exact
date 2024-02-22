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

TEST_SUITE_BEGIN("ILP input constraints");

TEST_CASE("multiplication simple") {
  Options opts;
  ILP ilp(opts);
  std::vector<IntVar*> vars;
  vars.reserve(5);
  vars.push_back(ilp.addVar("a", 0, 2, Encoding::LOG));
  vars.push_back(ilp.addVar("b", 0, 2, Encoding::LOG));
  IntVar* rhs = ilp.addVar("z", -10, 10, Encoding::LOG);

  ilp.addMultiplication(vars, rhs, rhs);

  CHECK(ilp.count(vars, true).second == 9);
  auto propres = ilp.propagate({rhs}, true);
  CHECK(propres == std::vector<std::pair<bigint, bigint>>{{0, 4}});
}

TEST_CASE("multiplication") {
  Options opts;
  ILP ilp(opts, true);
  std::vector<IntVar*> vars;
  vars.reserve(5);
  vars.push_back(ilp.addVar("a", -3, 4, Encoding::LOG));
  vars.push_back(ilp.addVar("b", -2, 5, Encoding::ORDER));
  vars.push_back(ilp.addVar("c", -1, 6, Encoding::ONEHOT));
  vars.push_back(ilp.addVar("d", 0, 1, Encoding::ORDER));
  vars.push_back(ilp.addVar("e", 2, 2, Encoding::ONEHOT));

  IntVar* rhs = ilp.addVar("z", -1000, 1000, Encoding::LOG);

  ilp.addMultiplication(vars, rhs, rhs);

  CHECK(ilp.count(vars, true).second == 1024);
  auto propres = ilp.propagate({rhs}, true);
  CHECK(propres == std::vector<std::pair<bigint, bigint>>{{-180, 240}});

  std::stringstream ss;
  ilp.printInput(ss);
  CHECK(ss.str() == "OBJ \nz[-1000,1000] =< 1*a[-3,4]*b[-2,5]*c[-1,6]*d[0,1]*e[2,2] =< z[-1000,1000]\n");
}

TEST_CASE("multiplication edge cases") {
  Options opts;
  ILP ilp(opts);

  IntVar* a = ilp.addVar("a", -2, 2, Encoding::ONEHOT);
  IntVar* y = ilp.addVar("y", -10, 10, Encoding::LOG);
  IntVar* z = ilp.addVar("z", -10, 10, Encoding::ORDER);
  IntVar* q = ilp.addVar("q", -10, 10, Encoding::LOG);
  IntVar* r = ilp.addVar("r", -10, 10, Encoding::ORDER);

  ilp.addMultiplication({}, q, r);
  ilp.addMultiplication({a}, y, z);

  auto propres = ilp.propagate({a, q, r, y, z}, true);
  CHECK(propres == std::vector<std::pair<bigint, bigint>>{{-2, 2}, {-10, 1}, {1, 10}, {-10, 2}, {-2, 10}});
}

TEST_SUITE_END();
