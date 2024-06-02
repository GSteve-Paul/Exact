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
#include "constraints/ConstrExp.hpp"

using namespace xct;

TEST_SUITE_BEGIN("IntProg inference tests");

TEST_CASE("subset sum") { CHECK(dp_subsetsum({11, 22, 33, 44, 55}, 100) == 99); }

/**

decdef Item as {"i" 1..4}.

declare has: Item -> bool.

declare value: Item -> {0..12}.
define value as {
  ("i1",2),
  ("i2",4),
  ("i3",6)
} default 0.

decdef cutoff as 11.

cutoff() <= sum[value(x) for x where Item(x) and has(x)].

@minimize sum[value(x) for x where Item(x) and has(x)].
*/

TEST_SUITE_END();
