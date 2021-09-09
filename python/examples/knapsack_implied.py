# This file is part of the Exact program
#
# Copyright (c) 2021 Jo Devriendt, KU Leuven
#
# Exact is distributed under the terms of the MIT License.
# You should have received a copy of the MIT License along with Exact.
# See the file LICENSE.

import math

# Construct a non-trivial integer knapsack instance
nvars = 10
var_range = range(1,nvars+1)
vars = [str(x) for x in var_range]
coefs_o = [5*x+(x%3) for x in var_range]
coefs_c = [5*x+(x%4) for x in var_range]
rhs_c = int(sum(coefs_c)*3/4)

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

# Add the variables. All have lower bound 0, but some have an upper bound of 1, others of 2.
for v in var_range:
    solver.addVariable(str(v),0,1+v%2)

# Add an auxiliary variable to turn off the objective function when the optimal is found.
solver.addVariable("aux",0,1)

# Add the knapsack constraint
success = solver.addConstraint(coefs_c, vars, True, rhs_c, False, 0)
# At this point, no UNSAT state should be entered, but it's better to check.
assert success
# success == 0 would denote that the added constraint triggered unsatisfiability.

# Initialize the solver with the knapsack objective, extended with the auxiliary variable.
# The first True parameter disables the automatic objective upper bounding, as otherwise finding an optimal solution
# may lead to an UNSAT state, at which point a new solver would need to be created to continue.
# The second False parameter disables the generation of auxiliary constraints that may reduce the set of optimal 
# solutions, as, in the worst case, one needs to generate all solutions to find their intersection, i.e., their 
# implied variable assignments.
solver.init(coefs_o+[1], vars+["aux"], False, False)

# Assume the auxiliary variable to 1, so that any solution found will have an objective value one higher than the 
# optimal objective value for the original knapsack problem.
solver.setAssumptions({"aux"},{1})

# Run the solver
print("run Exact:")
result = 1
while result!=0:
    result = solver.run()
    if result==1: # Corresponds to SolveState::SAT, so a solution has been found
        assert solver.hasSolution()
        # The solution may not be optimal, so add the corresponding objective bound constraint and continue search
        result = solver.boundObjByLastSol()
    if result==2: # Corresponds to SolveState::INCONSISTENT, so no solutions with the assumption "aux"=1 exist.
        # Check that indeed, the core consists of only the "aux" variable.
        assert solver.hasCore()
        assert list(solver.getLastCore()) == ["aux"]
        # If no solutions with the assumption "aux"=1 exist, the objective function can only be decreased by setting
        # "aux" to 0. Furthermore, as "aux" occurs only in the objective, but not any constraints, setting "aux"=0
        # will just yield the same solution as last time, which could not be improved except by setting "aux"=0.
        # Hence, the last solution is optimal, and the objective upper bound in the solver is exactly the optimal value
        # plus 1 (as "aux"=1 was true).
        optVal = solver.getObjectiveBounds()[1]-1
        print("optimal:",optVal)
        break

# To find more solutions, first remove the "aux"=1 assumption, as otherwise solver.run() would only return
# SolveState::INCONSISTENT.
solver.setAssumptions({'1'},{1})

propagatedBounds = [tuple(b) for b in solver.propagate(vars)]
print("Propagated:",{vars[i]:propagatedBounds[i] for i in range(0,len(vars)) if propagatedBounds[i]!=(0,1+(i+1)%2)})

# Note that the last objective bound added enforces any new solutions to be optimal. Even the last found solution, after
# projecting out the "aux" variable, is already optimal.

# Check that this last solution exists.
assert solver.hasSolution()

# Read out the last solution.
sol = solver.getLastSolutionFor(vars)

# To find the variable assignments implied by the set of optimal solutions, construct the intersection of those
# solutions. For now, the single optimal solution found initializes this intersection.
intersection = {vars[i]:sol[i] for i in range(0,len(vars))}

# Continue the search, forcing the solver to find solutions that reduce the intersection
solver.invalidateLastSol()
while result!=0:
    result = solver.run()
    if result==1: # Corresponds to SolveState::SAT, so a solution has been found
        assert solver.hasSolution()
        # Construct a list of the variables still in the intersection
        varlist = list(intersection.keys())
        # Get the values for these intersection variables
        sol = solver.getLastSolutionFor(varlist)
        # Reduce the intersection by only keeping those variables whose value matches that of the last found solution
        intersection = {varlist[i]:sol[i] for i in range(0,len(varlist)) if intersection[varlist[i]]==sol[i]}
        # Invalidate the last solution over the shrunk set of intersection variables
        result = solver.invalidateLastSol(intersection.keys())

# The solver is now in an UNSAT state, meaning that no solution exists that would differ from the current intersection
# Hence, the intersection is the set of implied assignments.
print("Implied:",intersection)
