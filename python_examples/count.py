# Import the exact package, e.g., from PyPI or self-compiled
import exact

# Create an Exact solver instance
solver = exact.Exact()

origvars = ["x", "y", "z"]
activators = ["a", "b", "c"]

for v in origvars + activators:
    solver.addVariable(v, 0, 1)

# Add the reified constraints
solver.addRightReification("a", True, [(1, "x"), (1, "y")], 1)
solver.addRightReification("b", True, [(1, "x"), (1, "z")], 1)
solver.addRightReification("c", True, [(1, "y"), (1, "z")], 1)


def count(assumptions):
    solver.clearAssumptions()
    solver.setAssumptions([(v, 1) for v in assumptions])
    print(solver.count(assumptions + origvars))


count(["a", "b", "c"])
count(["a", "b"])
count(["a", "c"])
count(["b", "c"])
