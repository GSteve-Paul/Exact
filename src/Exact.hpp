/**********************************************************************
This file is part of Exact.

Copyright (c) 2022 Jo Devriendt

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
#include "auxiliary.hpp"

class Exact {
  xct::ILP ilp;
  bool unsatState;

  xct::IntVar* getVariable(const std::string& name) const;
  std::vector<xct::IntVar*> getVariables(const std::vector<std::string>& names) const;

 public:
  /**
   * Create an instance of the Exact solver.
   */
  Exact();

  /**
   * Add a bounded integer variable.
   *
   * @param name: name of the variable
   * @param lb: lower bound
   * @param ub: upper bound
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addVariable(const std::string& name, long long lb, long long ub);
  void addVariable(const std::string& name, const std::string& lb, const std::string& ub);

  /**
   * Returns a list of variables added to the solver.
   *
   * @return the list of variables
   */
  std::vector<std::string> getVariables() const;

  /**
   * Add a linear constraint.
   *
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param useLB: whether or not the constraint is lower bounded
   * @param lb: the lower bound
   * @param useUB: whether or not the constraint is upper bounded
   * @param ub: the upper bound
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                     long long lb, bool useUB, long long ub);
  void addConstraint(const std::vector<std::string>& coefs, const std::vector<std::string>& vars, bool useLB,
                     const std::string& lb, bool useUB, const std::string& ub);

  /**
   * Add a reification of a linear constraint, where the head variable is true iff the constraint holds.
   *
   * @param head: Boolean variable that should be true iff the constraint holds
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param lb: lower bound of the constraint (a straightforward conversion exists if the constraint is upper bounded)
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addReification(const std::string& head, const std::vector<long long>& coefs,
                      const std::vector<std::string>& vars, long long lb);
  void addReification(const std::string& head, const std::vector<std::string>& coefs,
                      const std::vector<std::string>& vars, const std::string& lb);

  /**
   * Fix the value of a variable.
   *
   * Fixing the variable to different values will lead to unsatisfiability.
   *
   * @param iv: the variable to be fixed.
   * @param val: the value the variable is fixed to
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void fix(const std::string& var, long long val);
  void fix(const std::string& var, const std::string& val);

  /**
   * Set a list of assumptions under which a(n optimal) solution is found.
   *
   * If no such solution exists, a subset of the assumption variables will form a "core".
   * The assumptions over the variables in this core imply the non-existence of a solution to the constraints.
   * To reset the assumptions, pass two empty lists to this method.
   *
   * @param vars: the variables to assume
   * @param vals: the values assumed for the variables
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void setAssumptions(const std::vector<std::string>& vars, const std::vector<long long>& vals);
  void setAssumptions(const std::vector<std::string>& vars, const std::vector<std::string>& vals);

  /**
   * Initialize the solver with an objective function to be minimized.
   *
   * This function should be called exactly once, before the search.
   * Constraints can still be added after initialization is called.
   *
   * @param coefs: coefficients of the objective function
   * @param vars: variables of the objective function
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void init(const std::vector<long long>& coefs, const std::vector<std::string>& vars);
  void init(const std::vector<std::string>& coefs, const std::vector<std::string>& vars);

  /**
   * Start / continue the search.
   *
   * @return: one of four values:
   *
   * - SolveState::UNSAT (0): an inconsistency implied by the constraints has been detected. No more solutions exist,
   * and the search process is finished. No future calls should be made to this solver.
   * - SolveState::SAT (1): a solution consistent with the assumptions and the constraints has been found. The search
   * process can be continued, but to avoid finding the same solution over and over again, change the set of assumptions
   * or add a constraint invalidating this solution.
   * - SolveState::INCONSISTENT (2): no solutions consistent with the assumptions exist and a core has been constructed.
   * The search process can be continued, but to avoid finding the same core over and over again, change the set of
   * assumptions.
   * - SolveState::INPROCESSED (3): the search process just finished an inprocessing phase. The search process should
   * simply be continued, but control is passed to the caller to, e.g., change assumptions or add constraints.
   */
  SolveState runOnce();

  /**
   * Start / continue the search until an optimal solution or inconsistency is found.
   *
   * @return: one of two values:
   *
   * - SolveState::UNSAT (0): an inconsistency implied by the constraints has been detected. No (better) solutions
   * exist, and the search process is finished. No future calls should be made to this solver. An optimal solution can
   * be retrieved if one exists via hasSolution() and getLastSolutionFor().
   * - SolveState::INCONSISTENT (2): no solutions consistent with the assumptions exist and a core has been constructed.
   * The search process can be continued, but to avoid finding the same core over and over again, change the set of
   * assumptions. A core can be retrieved via hasCore() and getLastCore().
   */
  SolveState runFull();

  /**
   * Check whether a solution has been found.
   *
   * @return: whether a solution has been found.
   */
  bool hasSolution() const;

  /**
   * Get the values assigned to the given variables in the last solution.
   *
   * @param vars: the added variables for which the solution values should be returned.
   * @return: the solution values to the variables.
   *
   * Return arbitrarily large values using the string-based function variant '_arb'.
   */
  std::vector<long long> getLastSolutionFor(const std::vector<std::string>& vars) const;
  std::vector<std::string> getLastSolutionFor_arb(const std::vector<std::string>& vars) const;

  /**
   * Check whether a core -- a subset of the assumptions which cannot be extended to a solution -- has been found.
   *
   * @return: whether a core has been found.
   */
  bool hasCore() const;

  /**
   * The subset of assumption variables in the core. Their assumed values imply inconsistency under the constraints.
   *
   * @return: the variables in the core.
   */
  std::vector<std::string> getLastCore();

  /**
   * Add an upper bound to the objective function based on the objective value of the last found solution.
   */
  void boundObjByLastSol();

  /**
   * Add a constraint enforcing the exclusion of the last solution.
   */
  void invalidateLastSol();

  /**
   * Add a constraint enforcing the exclusion of the subset of the assignments in the last solution over a set of
   * variables.
   *
   * This can be useful in case a small number of variables determines the rest of the variables in each solution.
   *
   * @param vars: the variables for the sub-solution.
   */
  void invalidateLastSol(const std::vector<std::string>& vars);

  /**
   * Get the current lower and upper bound on the objective function.
   *
   * @return: the pair of bounds (lower, upper) to the objective.
   *
   * Return arbitrarily large values using the string-based function variant '_arb'.
   */
  std::pair<long long, long long> getObjectiveBounds() const;
  std::pair<std::string, std::string> getObjectiveBounds_arb() const;

  /**
   * Set the verbosity level of Exact's output.
   *
   * @param verbosity: the verbosity level, with 0 being silent and 1 being the default verbosity.
   */
  void setVerbosity(int verbosity);

  /**
   * Print Exact's internal statistics
   */
  void printStats();

  /**
   * Print Exact's internal formula.
   */
  void printFormula();

  /**
   * Under the assumptions set by setAssumptions, return implied lower and upper bound for the non-assumed variables in
   * vars. If no solution exists under the assumptions, return empty vector.
   *
   * @param vars: variables for which to calculate the implied bounds
   * @return: a pair of bounds for each variable in vars
   * @throw: UnsatEncounter exception in the case the instance is unsatisfiable. Propagation is undefined in this case.
   *
   * Return arbitrarily large values using the string-based function variant '_arb'.
   */
  std::vector<std::pair<long long, long long> > propagate(const std::vector<std::string>& vars);
  std::vector<std::pair<std::string, std::string> > propagate_arb(const std::vector<std::string>& vars);

  /**
   * Set solver options. Run with --help or look at Options.hpp to find the possible options.
   *
   * @param option: name of the option
   * @param value: value for the option encoded as a string. Boolean options, when passed, are set to true regardless of
   * this value.
   */
  void setOption(const std::string& option, const std::string& value);
};
