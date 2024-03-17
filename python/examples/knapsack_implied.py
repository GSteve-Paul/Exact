# This example showcases how to find the variable assignments implied by optimality, i.e., the variable assignments
# shared by all optimal solutions. A combination of the mechanics of assumption and solution invalidation allow to reuse
# the existing solver state (containing learned constraints) for optimal performance.

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
    solver.addVariable(str(v), lb(v), ub(v), "log")

# Add the knapsack constraint
solver.addConstraint(list(zip(coefs_c, vars)), True, rhs_c)

# Add an auxiliary 0-1 variable to turn off the objective function when the optimal is found.
solver.addVariable("aux")

# Set the knapsack objective, extended with the auxiliary variable.
solver.setObjective(list(zip(coefs_o + [1], vars + ["aux"])))

# Assume the auxiliary variable to 1, so that any solution found will have an objective value one higher than the 
# optimal objective value for the original knapsack problem.
solver.setAssumptions([("aux", 1)])

# Run the solver
print("run Exact:")
result = "PAUSED"
while result != "UNSAT":
    result = solver.runOnce()
    if result == "SAT":
        assert solver.hasSolution()
        # The solution may not be optimal, so add the corresponding objective bound constraint and continue search
        result = solver.boundObjByLastSol()
    if result == "INCONSISTENT":
        # Check that indeed, the core consists of only the "aux" variable.
        assert list(solver.getLastCore()) == ["aux"]
        # If no solutions with the assumption "aux"=1 exist, the objective function can only be decreased by setting
        # "aux" to 0. Furthermore, as "aux" occurs only in the objective, but not any constraints, setting "aux"=0
        # will just yield the same solution as last time, which could not be improved except by setting "aux"=0.
        # Hence, the last solution is optimal, and the objective upper bound in the solver is exactly the optimal value
        # plus 1 (as "aux"=1 was true).
        optVal = solver.getBestSoFar() - 1
        print("optimal:", optVal)
        break

# Note that the last objective bound added enforces any new solutions to be optimal. Even the last found solution, after
# projecting out the "aux" variable, is already optimal.

# Check that this last solution exists.
assert solver.hasSolution()

# Read out the last solution.
sol = solver.getLastSolutionFor(vars)

# To find the variable assignments implied by the set of optimal solutions, construct the intersection of those
# solutions. For now, the single optimal solution found initializes this intersection.
intersection = {vars[i]: sol[i] for i in range(0, len(vars))}

# To find more solutions, first remove the "aux"=1 assumption, as otherwise solver.runOnce() would only return
# SolveState::INCONSISTENT.
solver.clearAssumptions()

# Continue the search, forcing the solver to find solutions that reduce the intersection
solver.invalidateLastSol()
result = "PAUSED"
while result != "UNSAT":
    result = solver.runOnce()
    if result == "SAT":
        assert solver.hasSolution()
        # Construct a list of the variables still in the intersection
        varlist = list(intersection.keys())
        # Get the values for these intersection variables
        sol = solver.getLastSolutionFor(varlist)
        # Reduce the intersection by only keeping those variables whose value matches that of the last found solution
        intersection = {varlist[i]: sol[i] for i in range(0, len(varlist)) if intersection[varlist[i]] == sol[i]}
        # Invalidate the last solution over the shrunk set of intersection variables
        solver.invalidateLastSol(list(intersection.keys()))

# The solver is now in an UNSAT state, meaning that no solution exists that would differ from the current intersection
# Hence, the intersection is the set of implied assignments.
print("Implied:", intersection)
