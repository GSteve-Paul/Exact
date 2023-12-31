# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

# The following settings disable the generation of auxiliary constraints that may reduce the set of solutions,
# changing the counts we are interested in.
solver.setOption("inp-purelits", "0")
solver.setOption("inp-dombreaklim", "0")

origvars = ["x","y","z"]
activators = ["a","b","c"]

for v in origvars+activators:
    solver.addVariable(v, 0, 1)

# Add the reified constraints
solver.addRightReification("a", [1,1], ["x","y"], 1)
solver.addRightReification("b", [1,1], ["x","z"], 1)
solver.addRightReification("c", [1,1], ["y","z"], 1)

# Initialize the solver
solver.init([],[])

def count(assumptions):
    solver.clearAssumptions()
    for a in assumptions:
        solver.setAssumption(a,[1])
    print(solver.count(assumptions+origvars))

count(["a","b","c"])
count(["a","b","c"]) # this will yield 0, as all blocking clauses from the previous line will be "active"
count(["a","b"])
count(["a","c"])
count(["b","c"])
