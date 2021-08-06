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
#include "ILP.hpp"
#include "aux.hpp"

class Exact {
  std::unique_ptr<xct::ILP> ilp;

 public:
  Exact();

  State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                      long long lb, bool useUB, long long ub);
  State setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars);

  // std::vector<long long> getLastSolutionFor(const std::vector<std::string>& vars);
  // bool hasLowerBound();
  // long long getLowerBound();
  // bool hasUpperBound();
  // long long getUpperBound();

  void init();

  void run();
};
