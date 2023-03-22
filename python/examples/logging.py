# Prove the clausal decomposition of x+y+z >= 2

import sys
import math

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()
solver.setOption("proof-log","/tmp/logging_example") # NOTE: should be set before calling init(), and init() should be called before adding constraints
# Proof logging only works for pure satisfiability problems without the following options:
solver.setOption("inp-purelits", "0")
solver.setOption("inp-dombreaklim", "0")

# initialize Exact
solver.init([], [])

# Add the variables
variables = ["x","y","z","w"]

for v in variables:
    solver.addVariable(v, 0, 1)

# Add the constraint x + y - z >= 1
solver.addConstraint([1,1,-1], ["x","y","z"], True, 1, False, 0)
# Add the constraint w - y + z >= 0
solver.addConstraint([1,-1,1], ["w","y","z"], True, 0, False, 0)

# check whether !y | !z is an implied clause
solver.setAssumption("y", [1])
solver.setAssumption("z", [1])
state = solver.runFull(False)
assert(state==1) # SAT, so not an implied clause

# check whether x | w is an implied clause
solver.clearAssumptions()
solver.setAssumption("x", [0])
solver.setAssumption("w", [0])
state = solver.runFull(False)
assert(state==2) # inconsistent with assumptions
