# This example builds on 3_implications_simple.py by adding assumptions into the mix.
# We solve the knapsack implication problem under the assumption that every other variable must take the value 0.

# Import the exact package, e.g., from PyPI or self-compiled
import exact

# Create an Exact solver instance
solver = exact.Exact()

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

# Add the variables with various lower bounds.
for v in var_range:
    solver.addVariable(str(v), lb(v), ub(v))

# Add the knapsack constraint
solver.addConstraint(list(zip(coefs_c, vars)), True, rhs_c)

# Set the knapsack objective
solver.setObjective(list(zip(coefs_o, vars)))

# Assume that every other variable is zero
assumptions = [(str(v), 0) for v in var_range if v%2==1]
solver.setAssumptions(assumptions)

# Get the optimum value
print("run Exact:")
state, optval = solver.toOptimum()
assert state == "SAT"
print("Optimal:", optval)
# fix the optimum value
solver.addConstraint(list(zip(coefs_o, vars)), True, optval, True, optval)

# Calculate the variable bounds shared by the set of optimal solutions under the assumptions
state, propagatedBounds = solver.propagate(vars)
print(state)
assert state == "SAT"
print("Propagated bounds:",
      {vars[i]: propagatedBounds[i] for i in range(0, len(vars)) if propagatedBounds[i] != (lb(i+1), ub(i+1))})
