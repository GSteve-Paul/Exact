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

  xct::IntVar* getVariable(const std::string& name);

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
   */
  void addVariable(const std::string& name, long long lb, long long ub);

  /**
   * Returns a list of variables added to the solver.
   *
   * @return the list of variables
   */
  std::vector<std::string> getVariables() const;

  /**
   * The given bounds of a previously added variable.
   * @param var: the variable under consideration.
   * @return: the pair of bounds (lower, upper) to the variable.
   */
  std::pair<long long, long long> getBounds(const std::string& var) const;

  /**
   * Add a linear constraint.
   *
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param useLB: whether or not the constraint is lower bounded
   * @param lb: the lower bound
   * @param useUB: whether or not the constraint is upper bounded
   * @param ub: the upper bound
   * @return: State::SUCCESS (1) or State::UNSAT (0) to denote whether the constraint yielded unsatisfiability.
   */
  State addConstraint(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool useLB,
                      long long lb, bool useUB, long long ub);

  /**
   * Add a reification of a linear constraint, where the head variable is true iff the constraint holds.
   *
   * @param head: Boolean variable that should be true iff the constraint holds
   * @param coefs: coefficients of the constraint
   * @param vars: variables of the constraint
   * @param lb: lower bound of the constraint (a straightforward conversion exists if the constraint is upper bounded)
   * @return: State::UNSAT (0) or State::SUCCESS (1) to denote whether the added constraint yielded unsatisfiability.
   */
  State addReification(const std::string& head, const std::vector<long long>& coefs,
                       const std::vector<std::string>& vars, long long lb);

  /**
   * Set a list of assumptions under which a(n optimal) solution is found.
   *
   * If no such solution exists, a subset of the assumption variables will form a "core".
   * The assumptions over the variables in this core imply the non-existence of a solution to the constraints.
   * To reset the assumptions, pass two empty lists to this method.
   *
   * @param vars: the variables to assume
   * @param vals: the values assumed for the variables
   */
  void setAssumptions(const std::vector<std::string>& vars, const std::vector<long long>& vals);

  /**
   * Initialize the solver with an objective function to be minimized.
   *
   * This function should be called exactly once, before the search.
   * Constraints can still be added after initialization is called.
   *
   * @param coefs: coefficients of the objective function
   * @param vars: variables of the objective function
   * @param boundObjective: automatically add an upper bound constraint to the objective function for each solution
   * found during search. This guarantees each solution will improve on the best-so-far, but will also yield UNSAT
   * when the last solution is proven to be optimal.
   * @param addNonImplieds: allow the solver to derive non-implied constraints that are consistent with at least
   * one optimal solution. A simple example is fixing pure literals, which occur only positively or negatively in the
   * constraints. These non-implied constraints speed up search by reducing the set of solutions.
   */
  void init(const std::vector<long long>& coefs, const std::vector<std::string>& vars, bool boundObjective,
            bool addNonImplieds);

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
  SolveState run();

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
   */
  std::vector<long long> getLastSolutionFor(const std::vector<std::string>& vars) const;

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
  std::vector<std::string> getLastCore() const;

  /**
   * Add an upper bound to the objective function based on the objective value of the last found solution.
   *
   * @return: State::UNSAT (0) or State::SUCCESS (1) to denote whether the added constraint yielded unsatisfiability.
   */
  State boundObjByLastSol();

  /**
   * Add a constraint enforcing the exclusion of the last solution.
   *
   * @return: State::UNSAT (0) or State::SUCCESS (1) to denote whether the added constraint yielded unsatisfiability.
   */
  State invalidateLastSol();

  /**
   * Add a constraint enforcing the exclusion of the subset of the assignments in the last solution over a set of
   * variables.
   *
   * This can be useful in case a small number of variables determines the rest of the variables in each solution.
   *
   * @param vars: the variables for the sub-solution.
   * @return: State::UNSAT (0) or State::SUCCESS (1) to denote whether the added constraint yielded unsatisfiability.
   */
  State invalidateLastSol(const std::vector<std::string>& vars);

  /**
   * Get the current lower and upper bound on the objective function.
   *
   * @return: the pair of bounds (lower, upper) to the objective.
   */
  std::pair<long long, long long> getObjectiveBounds() const;

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

  std::vector<std::pair<long long, long long> > propagate(const std::vector<std::string>& varnames);
};
