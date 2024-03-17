# This example showcases the builtin propagate method, which returns implied variable bounds under given assumptions.
# The first part is identical to knapsack_implied.py, generating a state of the solver where all solutions are optimal.
# The second part consists of the last lines, which calculate the variable bounds that hold for all optimal solutions.

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

# Set the knapsack objective
solver.setObjective(list(zip(coefs_o, vars)))

# Get the optimum value
print("run Exact:")
state = solver.runFull(True)
assert state=="UNSAT"
print("optimal", solver.getBestSoFar())
