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
  xct::ILP ilp;

 public:
  Exact();

  State addVariable(const std::string& name, long long lb, long long ub);
  std::vector<std::string> getVariables() const;
  State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                      long long lb, bool useUB, long long ub);
  State setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars);
  State setAssumptions(const std::vector<std::string>& vars, const std::vector<long long>& vals);
  State boundObjByLastSol();
  State invalidateLastSol();
  State invalidateLastSol(const std::vector<std::string>& vars);
  void printFormula();

  void init(bool boundObjective, bool addNonImplieds);
  SolveState run();

  std::pair<long long, long long> getObjectiveBounds() const;
  std::pair<long long, long long> getBounds(const std::string& var) const;

  bool hasSolution() const;
  std::vector<long long> getLastSolutionFor(const std::vector<std::string>& vars) const;
  bool hasCore() const;
  std::vector<std::string> getLastCore() const;

  void printStats();
  void setVerbosity(int verbosity);
};
