# Construct a verifiable proof that x | w is implied by
# x + y - z >= 1
# w - y + z >= 0

# Import the exact package
import exact

# Create an Exact solver instance with two options
solver = exact.Exact([("proof-log", "/tmp/logging_example"), ("proof-assumptions", "0")])
# The first option activates proof logging by passing a filepath. This will generate a .formula and .proof file, which
# can be verified by VeriPB (https://gitlab.com/MIAOresearch/software/VeriPB)
# The second option disables advanced solver routines that introduce unverifiable assumptions in the proof

# Add the 0-1 variables
variables = ["x", "y", "z", "w"]
for v in variables:
    solver.addVariable(v)

# Add the constraint x + y - z >= 1
solver.addConstraint([(1, "x"), (1, "y"), (-1, "z")], True, 1)
# Add the constraint w - y + z >= 0
solver.addConstraint([(1, "w"), (-1, "y"), (1, "z")], True, 0)

# check whether !y | !z is an implied clause
solver.setAssumptions([("y", 1), ("z", 1)])
state = solver.runFull(False)
assert state == "SAT"  # so not an implied clause

# check whether x | w is an implied clause
solver.clearAssumptions()
solver.setAssumptions([("x", 0), ("w", 0)])
state = solver.runFull(False)
assert state == "INCONSISTENT"  # inconsistent with assumptions

print("All clear!")
print("You can now run VeriPB on the generated files, e.g.:")
print("veripb /tmp/logging_example.formula /tmp/logging_example.proof")
