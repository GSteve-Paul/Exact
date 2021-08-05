/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include <string>
#include <vector>
#include "aux.hpp"

int start();

State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB, long long lb,
                    bool useUB, long long ub);
