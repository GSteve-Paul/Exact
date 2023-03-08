# This file is part of the Exact program
#
# Copyright (c) 2021 Jo Devriendt, KU Leuven
#
# Exact is distributed under the terms of the MIT License.
# You should have received a copy of the MIT License along with Exact.
# See the file LICENSE.

# This example showcases the builtin propagate method, which returns implied variable bounds under given assumptions.
# The first part is identical to knapsack_implied.py, generating a state of the solver where all solutions are optimal.
# The second part consists of the last lines, which calculate the variable bounds that hold for all optimal solutions.


import sys
# Get the encoding for integer variables from the command line if available
encoding = "log" if len(sys.argv)<2 else sys.argv[1]

def lb(v):
    return -(v%3)
def ub(v):
    return 1+v%2

# Construct a non-trivial integer knapsack instance
nvars = 50
var_range = range(1, nvars + 1)
vars = [str(x) for x in var_range]
coefs_o = [5 * x + (x % 4) for x in var_range]
coefs_c = [5 * x + (x % 5) for x in var_range]
rhs_c = int(sum(coefs_c) / 3)

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

# Add the variables. All have lower bound 0, but some have an upper bound of 1, others of 2.
for v in var_range:
    solver.addVariable(str(v), lb(v), ub(v), encoding)

# Add an auxiliary variable to turn off the objective function when the optimal is found.
solver.addVariable("aux", 0, 1)

# Add the knapsack constraint
solver.addConstraint(coefs_c, vars, True, rhs_c, False, 0)

# Initialize the solver with the knapsack objective, extended with the auxiliary variable.
solver.init(coefs_o + [1], vars + ["aux"])

# Disable the automatic objective upper bounding. We will add these upper bounds manually to prevent that finding an
# optimal solution yields an UNSAT state - no useful further inferences can be made with a solver in an UNSAT state.
solver.setOption("opt-boundupper", "0")
# The following settings disable the generation of auxiliary constraints that may reduce the set of optimal solutions,
# as we are interested in finding the intersection of all optimal solutions - i.e., the implied variable assignments.
solver.setOption("inp-purelits", "0")
solver.setOption("inp-dombreaklim", "0")

# Assume the auxiliary variable to 1, so that any solution found will have an objective value one higher than the 
# optimal objective value for the original knapsack problem.
solver.setAssumption("aux", {1})

# Run the solver
print("run Exact:")
result = 1
while result != 0:
    result = solver.runOnce()
    if result == 1:  # Corresponds to SolveState::SAT, so a solution has been found
        assert solver.hasSolution()
        # The solution may not be optimal, so add the corresponding objective bound constraint and continue search
        result = solver.boundObjByLastSol()
    if result == 2:  # Corresponds to SolveState::INCONSISTENT, so no solutions with the assumption "aux"=1 exist.
        # Check that indeed, the core consists of only the "aux" variable.
        assert solver.hasCore()
        assert list(solver.getLastCore()) == ["aux"]
        # If no solutions with the assumption "aux"=1 exist, the objective function can only be decreased by setting
        # "aux" to 0. Furthermore, as "aux" occurs only in the objective, but not any constraints, setting "aux"=0
        # will just yield the same solution as last time, which could not be improved except by setting "aux"=0.
        # Hence, the last solution is optimal, and the objective upper bound in the solver is exactly the optimal value
        # plus 1 (as "aux"=1 was true).
        optVal = solver.getObjectiveBounds()[1] - 1
        print("optimal:", optVal)
        break

# Clear aux assumption to fix objective to optimal value
solver.clearAssumptions()

# Propagate under a simple assumption:
solver.setAssumption("1",{1})

# Calculate the variable bounds shared by the set of optimal solutions under the assumptions
propagatedBounds = [tuple(b) for b in solver.propagate(vars)]
print("Propagated:",
     {vars[i]: propagatedBounds[i] for i in range(0, len(vars)) if propagatedBounds[i] != (lb(i+1), ub(i+1))})
