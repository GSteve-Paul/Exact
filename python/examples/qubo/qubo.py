# Problem: https://en.wikipedia.org/wiki/Quadratic_unconstrained_binary_optimization

#!/usr/bin/python

import sys

if len(sys.argv)==2:
    problem = sys.argv[1]
else:
    print("Usage: python3 qubo.py <problem file>")
    print("Using default arguments: python3 python/examples/qubo/qubo.py python/examples/qubo/bqp50.1")
    print("More files can be found at https://github.com/rliang/qubo-benchmark-instances")
    problem = "python3 python/examples/qubo/qubo.py python/examples/qubo/bqp50.1"

orig_vars = -1
terms = [] # [coef [vars]]
aux_vars = -1
maxvar = -1

# read graph
with open(problem) as f:
    lines = f.readlines() # list containing lines of file
    aux_vars = len(lines)-1
    for l in lines:
        if orig_vars == -1:
            orig_vars = int(l)
        else:
            nums = [int(x) for x in l.split()]
            terms += [(nums[-1],nums[:-1])]
            maxvar = max([maxvar]+terms[-1][1])

assert(aux_vars == len(terms))
assert(maxvar == orig_vars-1) # 0-based orig_vars

print(terms)

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

for v in range(1,orig_vars+aux_vars+1):
    solver.addVariable(str(v),0,1)

objective = []
aux = orig_vars
for t in terms:
    nvars = len(t[1])
    if nvars > 1:
        aux += 1
        objective += [str(aux)]
        varlist = [str(v+1) for v in t[1]]+[str(aux)]
        solver.addConstraint([-1]*nvars+[1],varlist,True,1-nvars,False,0)
        solver.addConstraint([1]*nvars+[-nvars],varlist,True,0,False,0)
    else:
        objective += [str(t[1][0])]

# initialize the solver without an objective function
solver.init([t[0] for t in terms], objective)

printNoSolve = False

if printNoSolve:
    solver.printFormula()
else:
    # Run the solver
    print("run Exact:")
    solver.runFull()
    if solver.hasSolution():
        print("SAT")
    else:
        print("UNSAT")
    solver.printStats()
