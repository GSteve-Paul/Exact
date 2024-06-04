# This example builds on 4_assumptions.py by using one-hot encoded variables.
# For large domains, one-hot encoded variables are slower than log-encoded variables.
# However, the one-hot encoding firstly allows to pass a list of multiple allowed values as assumption for a variable.
# Secondly, we can prune the possible values (the domains) of a variable under the current assumptions with
# pruneDomains(). This is more fine-grained than the bounds on the domains given by the propagate() function.

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

# Add the variables with various lower bounds using a one-hot
for v in var_range:
    solver.addVariable(str(v), lb(v), ub(v), "onehot")

# Add the knapsack constraint
solver.addConstraint(list(zip(coefs_c, vars)), True, rhs_c)

# Set the knapsack objective
solver.setObjective(list(zip(coefs_o, vars)))

# Assume that a variable can only take non-zero values in their range
assumptions = [(str(v), [val for val in range(lb(v), ub(v)+1) if val!=0]) for v in var_range]
solver.setAssumptionsList(assumptions)

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

# Instead of bound propagation, let's prune the domains of the variables, a priori excluding 0
# Note that this requires a one-hot encoding of the variables
state, prunedDomains = solver.pruneDomains(vars)
assert state == "SAT"
print("Pruned domains:",
      {vars[i]: [j for j in prunedDomains[i]] for i in range(0, len(vars)) if len(prunedDomains[i]) != ub(i+1)-lb(i+1)})
