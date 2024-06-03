# This example showcases how to solve an integer classic knapsack problem with Exact's Python interface.

# Import the exact package, e.g., from PyPI or self-compiled
import exact

# Create an Exact solver instance
solver = exact.Exact()

# Construct a non-trivial integer knapsack instance
nvars = 50
var_range = range(1, nvars + 1)
vars = [str(x) for x in var_range]
coefs_o = [5 * x + (x % 3) for x in var_range]
coefs_c = [5 * x + (x % 4) for x in var_range]
rhs_c = int(sum(coefs_c) * 3 / 4)

# Add the variables. All have lower bound 0, but some have an upper bound of 1, others of 2.
for v in var_range:
    solver.addVariable(str(v), 0, 1 + v % 2)

# Add the knapsack constraint
solver.addConstraint(list(zip(coefs_c, vars)), True, rhs_c)

solver.setObjective(list(zip(coefs_o, vars)))

# Run the solver to completion
print("Running Exact...")
result = solver.runFull(True)
print("Answer:", result)

# Check that the solution exists.
print("Solution found:", solver.hasSolution())

# Print the final objective value
print("Optimal value:", solver.getBestSoFar())

# Print the final dual value
print("Objective dual bound:", solver.getDualBound())

# Print the last solution.
sol = solver.getLastSolutionFor(vars)
print("Solution:", sol)

# And calculate its optimal value by hand for good measure.
print("Sanity check:", sum([sol[i] * coefs_o[i] for i in range(0, len(coefs_o))]))
