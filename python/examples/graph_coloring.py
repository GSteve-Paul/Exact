#!/usr/bin/python

import sys

# usage: python3 graph_colorying.py <adjacency matrix file> <number of colors>
# example usage: python3 graph_coloring.py graph_77v-7chrom_adj_matrix.txt 5

nodes = 0;
edges = [];
colors = int(sys.argv[2])

with open(sys.argv[1]) as f:
    lines = f.readlines() # list containing lines of file
    nodes = len(lines);
    for l in lines:
        edges += [[x=='1' for x in l[:-1]]]
        assert(len(edges[-1])==nodes)

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

def toVar(n,c):
    return "col("+str(n)+")="+str(c)

# Add the variables. All have lower bound 0, but some have an upper bound of 1, others of 2.
for n in range(0,nodes):
    for c in range(0,colors):
        solver.addVariable(toVar(n,c),0,1)

# Every node has exactly one color
for n in range(0,nodes):
    solver.addConstraint([1]*colors,[toVar(n,c) for c in range(0,colors)],True,1,True,1)

# If there is an edge between two nodes, at most one of them has a given color c
for n1 in range(0,nodes):
    for n2 in range(n1+1,nodes):
        if edges[n1][n2]:
            for c in range(0,colors):
                solver.addConstraint([1,1],[toVar(n1,c),toVar(n2,c)],False,0,True,1)

# Add color symmetry breakers
symmax = nodes
for c in range(0,colors-1):
    cf = int(round(pow(2, symmax)))
    coefs = []
    vs = []
    for n in range(0,symmax):
        vs += [toVar(n,c), toVar(n,c+1)]
        coefs+=[str(-cf),str(cf)]
        cf //= 2
    assert(cf==1)
    solver.addConstraint(coefs,vs,True,"0",False,"")

# initialize the solver without an objective function
solver.init([], [], False, True)

# solver.printFormula()

# Run the solver
print("run Exact:")
result = 3
while result==3:
    # As long as the result is not UNSAT (== 0), the solver is kept running.
    result = solver.run()
# Once the loop exits, the last found solution is the optimal one.

if result == 1:
    print("SAT")
elif result == 0:
    print("UNSAT")
else:
    print("UNEXPECTED RESULT")
