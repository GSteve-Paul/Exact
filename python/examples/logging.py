# Prove that x | w is implied by x + y - z >= 1 & w - y + z >= 0

import sys
import math

# Import the exact package
import exact

# Create an Exact solver instance
solver = exact.Exact()
# Activate the proof logging option by passing a filepath. This will generate a .formula and .proof file, which can be
# verified by VeriPB (https://github.com/StephanGocht/VeriPB)
# NOTE: the proof logging option should be activated BEFORE calling init(), and init() should be called BEFORE adding constraints
solver.setOption("proof-log","/tmp/logging_example")
# Proof logging only works for pure satisfiability problems with the following options:
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

# now you can run VeriPB on the generated files, e.g.:
# veripb /tmp/logging_example.formula /tmp/logging_example.proof

# The following (nonsensical) constraint addition yields the line
# red +1 ~x2 +1 ~x4 >= 2 ; x4 1 x2 ~x3
# in the .proof file.
solver.addConstraint([-1,-1], ["w","y"], True, 0, False, 0,["w","y"],[True,False],["","z"])