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
   *
   * @param: list of pairs of option names and values for the option, both encoded as a string. Run with --help or look
   * at Options.hpp to find the possible options. Options without an argument are activated regardless of any value.
   */
  Exact(const std::vector<std::pair<std::string, std::string>>& options = {});

  /**
   * Add a bounded integer variable.
   *
   * @param name: name of the variable
   * @param lb: lower bound
   * @param ub: upper bound
   * @param encoding: none, "log", "order" or "onehot"
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addVariable(const std::string& name, long long lb, long long ub, const std::string& encoding = "");
  void addVariable(const std::string& name, const std::string& lb, const std::string& ub,
                   const std::string& encoding = "");

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
   * Add a reification of a linear constraint, where the constraint holds if the head variable is true.
   *
   * @param head: Boolean variable
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param lb: lower bound of the constraint (a straightforward conversion exists if the constraint is upper bounded)
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addRightReification(const std::string& head, const std::vector<long long>& coefs,
                           const std::vector<std::string>& vars, long long lb);
  void addRightReification(const std::string& head, const std::vector<std::string>& coefs,
                           const std::vector<std::string>& vars, const std::string& lb);

  /**
   * Add a reification of a linear constraint, where the head variable is true if the constraint holds.
   *
   * @param head: Boolean variable
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param lb: lower bound of the constraint (a straightforward conversion exists if the constraint is upper bounded)
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void addLeftReification(const std::string& head, const std::vector<long long>& coefs,
                          const std::vector<std::string>& vars, long long lb);
  void addLeftReification(const std::string& head, const std::vector<std::string>& coefs,
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
   * Set assumptions for a single variable under which a(n optimal) solution is found. These assumptions enforce that
   * the given variable can take only the given values, overriding any previous assumed restrictions on this variable.
   * Assumptions for other variables are left untouched.
   *
   * If no such solution exists, a subset of the assumption variables will form a "core" provided by "getLastCore()".
   *
   * @param var: the variable to assume
   * @param vals: the possible values remaining for this variable
   * @pre: the set of possible values is not empty
   * @pre: if the number of distinct possible values is larger than one and smaller than the range of the variable, then
   * the variable uses a one-hot encoding. As a consequence, for Boolean variables the encoding does not matter.
   * @pre: the given values are within the bounds of the variable
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void setAssumption(const std::string& var, const std::vector<long long>& vals);
  void setAssumption(const std::string& var, const std::vector<std::string>& vals);

  /**
   * Clears all assumptions.
   */
  void clearAssumptions();

  /**
   * Clears all assumptions for the given variables.
   *
   * @param var: the variable to clear the assumptions for.
   */
  void clearAssumption(const std::string& var);

  /**
   * Check whether a given variable has any assumed restrictions in the possible values it can take.
   *
   * @param var: the variable to check
   * @return: true if the variable has assumed restrictions, false if not
   */
  bool hasAssumption(const std::string& var) const;

  /**
   * Get the possible values not restricted by the currently set assumptions for a given variable.
   *
   * This method is mainly meant for diagnostic purposes and is not very efficient.
   *
   * @param var: the variable under inspection
   * @return: the values of the variable that are *not* restricted
   *
   * Return arbitrarily large values using the string-based function variant '_arb'.
   */
  std::vector<long long> getAssumption(const std::string& var) const;
  std::vector<std::string> getAssumption_arb(const std::string& var) const;

  /**
   * Set solution hints for a list of variables. These hints guide the solver to prefer a solution with those values.
   * Internally, this is done by the search heuristic trying to assign the hinted value when making a search decision.
   *
   * @param vars: the variables to set the hint for
   * @param vals: the hinted values for the variables
   * @pre: vars and vals have the same size
   * @pre: the given values are within the bounds of the corresponding variables
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void setSolutionHints(const std::vector<std::string>& vars, const std::vector<long long>& vals);
  void setSolutionHints(const std::vector<std::string>& vars, const std::vector<std::string>& vals);

  /**
   * Clears solution hints for the given variables
   *
   * @param vars: the variables to clear the hint for.
   */
  void clearSolutionHints(const std::vector<std::string>& vars);

  /**
   * Pass an objective function to be minimized.
   *
   * This function can be called multiple times, replacing the previous objective with the new one.
   * Any constraints implied by the previous objective are *not* removed. If this is desired, add an auxiliary variable
   * to the objective that can disable objective bounds. E.g., if the objective is x+2y+3z, then adding the auxiliary
   * variable a with coefficient 6 and assuming it to true will allow the invalidation of any objective bound later on
   * by fixing it to false.
   * I.e., any bound on x+2y+3z+6a with a assumed to true will have at least 6 as upper bound, and fixing a to false
   * will satisfy any such upper bound, in effect disabling the upper bound constraints.
   *
   * @param coefs: coefficients of the objective function
   * @param vars: variables of the objective function
   *
   * Pass arbitrarily large values using the string-based function variant.
   */
  void setObjective(const std::vector<long long>& coefs, const std::vector<std::string>& vars, long long offset = 0);
  void setObjective(const std::vector<std::string>& coefs, const std::vector<std::string>& vars,
                    const std::string& offset = "0");

  /**
   * Start / continue the search.
   *
   * @return: one of four values:
   *
   * - SolveState::UNSAT (0): an inconsistency implied by the constraints has been detected. No more solutions exist,
   * and the search process is finished. No future calls should be made to this solver.
   * - SolveState::SAT (1): a solution consistent with the assumptions and the constraints has been found. The search
   * process can be continued, but to avoid finding the same solution over and over again, change the set of assumptions
   * or add a constraint invalidating this solution via boundObjByLastSol().
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
   * @ param optimize: whether to optimize for the given objective. If optimize is true, SAT answers will be handled
   * by adding an objective bound constraint, until unsatisfiability is reached, in which case the last found solution
   * (if it exists) is the optimal one. If optimize is false, control will be handed back to the caller, without an
   * objective bound constraint being added.
   * @param timeout: a (rough) timeout limit in seconds. The solver state is still valid after hitting timeout. It may
   * happen that an internal routine exceeds timeout without returning for a while, but it should return eventually. A
   * value of 0 disables the timeout.
   *
   * @return: one of three values:
   *
   * - SolveState::UNSAT (0): an inconsistency implied by the constraints has been detected. No (better) solutions
   * exist, and the search process is finished. No future calls should be made to this solver. An optimal solution can
   * be retrieved if one exists via hasSolution() and getLastSolutionFor().
   * - SolveState::SAT (1): a solution consistent with the assumptions and the constraints has been found. The search
   * process can be continued, but to avoid finding the same solution over and over again, change the set of assumptions
   * or add a constraint invalidating this solution. This answer will not be returned if optimize is true.
   * - SolveState::INCONSISTENT (2): no solutions consistent with the assumptions exist and a core has been constructed.
   * The search process can be continued, but to avoid finding the same core over and over again, change the set of
   * assumptions. A core can be retrieved via hasCore() and getLastCore().
   * - SolveState::TIMEOUT (3): the timeout was reached. Solving can be resumed with a later call.
   */
  SolveState runFull(bool optimize, double timeout = 0);

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
   * When UNSAT is reached, the last core will be empty.
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
   * Print Exact's internal statistics
   */
  void printStats();

  /**
   * Print variables given to Exact.
   */
  void printVariables() const;

  /**
   * Print objective and constraints given to Exact.
   */
  void printInput() const;

  /**
   * Print Exact's internal formula.
   */
  void printFormula();

  /**
   * Under previously set assumptions, return implied lower and upper bound for variables in vars. If no
   * solution exists under the assumptions, return empty vector.
   *
   * @param vars: variables for which to calculate the implied bounds
   * @param timeout: a (rough) timeout limit in seconds. The solver state is still valid after hitting timeout. It may
   * happen that an internal routine exceeds timeout without returning for a while, but it should return eventually. A
   * value of 0 disables the timeout.
   * @pre: the problem is not unsatisfiable
   * @return: a list of pairs of bounds for each variable in vars. This list is empty if timeout is reached or the
   * problem is unsatisfiable or inconsistent under the current assumptions.
   *
   * Return arbitrarily large bounds using the string-based function variant '_arb'.
   */
  std::vector<std::pair<long long, long long>> propagate(const std::vector<std::string>& vars, double timeout = 0);
  std::vector<std::pair<std::string, std::string>> propagate_arb(const std::vector<std::string>& vars,
                                                                 double timeout = 0);

  /**
   * Under previously set assumptions, derive domains for the given variables where all impossible values are pruned.
   * If no solution exists for the given domains under the current assumptions, all returned domains will be empty.
   *
   * @param vars: variables for which to calculate the pruned domains
   * @param timeout: a (rough) timeout limit in seconds. The solver state is still valid after hitting timeout. It may
   * happen that an internal routine exceeds timeout without returning for a while, but it should return eventually. A
   * value of 0 disables the timeout.
   * @pre: the problem is not unsatisfiable
   * @pre: all variables use the one-hot encoding or have a domain size of 2
   * @return: pruned domains for each variable in vars. This list is empty if timeout is reached. This list contains
   * empty domains for all variables if the problem is unsatisfiable or inconsistent under the current assumptions.
   *
   * Return arbitrarily large domain values using the string-based function variant '_arb'.
   */
  std::vector<std::vector<long long>> pruneDomains(const std::vector<std::string>& vars, double timeout = 0);
  std::vector<std::vector<std::string>> pruneDomains_arb(const std::vector<std::string>& vars, double timeout = 0);

  /**
   * Under previously set assumptions, return number of different solutions projected to vars.
   *
   * @param vars: variables for which to calculate different solutions
   * @param timeout: a (rough) timeout limit in seconds. The solver state is still valid after hitting timeout. It may
   * happen that an internal routine exceeds timeout without returning for a while, but it should return eventually. A
   * value of 0 disables the timeout.
   * @return: an integer value
   */
  long long count(const std::vector<std::string>& vars, double timeout = 0);

  // TODO: void getStat()
};
