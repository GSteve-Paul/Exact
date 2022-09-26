#!/usr/bin/python

import sys
import networkx as nx

# usage: python3 graph_colorying.py <adjacency matrix file> <number of colors> <symmetry file> <print instead of solve>
# example usage: python3 graph_coloring.py graph_77v-7chrom_adj_matrix.txt 5 graph_77v-7chrom_symmetries.txt 0

nodes = 0
edges = []
colors = int(sys.argv[2])
symmetries = []
printNoSolve = bool(int(sys.argv[4]))

# read graph
with open(sys.argv[1]) as f:
    lines = f.readlines() # list containing lines of file
    nodes = len(lines)
    for l in lines:
        edges += [[x=='1' for x in l[:-1]]]
        assert(len(edges[-1])==nodes)

# read symmetries
with open(sys.argv[3]) as f:
    lines = f.readlines()
    for l in lines:
        # continue
        sym = [x for x in range(0,nodes)]
        cycles = l.split(')')[:-1] # pops \n
        for cycle in cycles:
            images = [int(x)-1 for x in cycle[1:].split(',')] # pops (
            n = len(images)
            for i in range(0,n):
                sym[images[i]]=images[(i+1)%n]
        symmetries += [sym]

# check symmetries
for sym in symmetries:
    for n1 in range(0,nodes):
        for n2 in range(n1+1,nodes):
            assert(edges[n1][n2]==edges[sym[n1]][sym[n2]])

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

# Instead of adding a clause for each two edges, we add an at-most-one constraint for each maximal clique
G = nx.Graph()
for n1 in range(0,nodes):
    for n2 in range(n1+1,nodes):
        if edges[n1][n2]:
            G.add_edge(n1,n2)

for clique in nx.find_cliques(G):
    for c in range(0,colors):
        solver.addConstraint([1]*len(clique),[toVar(n,c) for n in clique],False,0,True,1)

# If there is an edge between two nodes, at most one of them has a given color c
# for n1 in range(0,nodes):
#     for n2 in range(n1+1,nodes):
#         if edges[n1][n2]:
#             for c in range(0,colors):
#                 solver.addConstraint([1,1],[toVar(n1,c),toVar(n2,c)],False,0,True,1)

# Add graph symmetry breakers
for sym in symmetries:
    vs = []
    for n in range(0,nodes):
        if n>=sym[n]: continue # already handled
        for c in range(0,colors):
            vs += [toVar(n,c),toVar(sym[n],c)]
    coefs = []
    cf = int(round(pow(2,len(vs)//2)))
    for i in range(0,len(vs)//2):
        coefs += [str(-cf),str(cf)]
        cf //= 2
    assert(cf==1)
    solver.addConstraint(coefs,vs,True,"0",False,"")

# Add color symmetry breakers
for c in range(0,colors-1):
    cf = int(round(pow(2, nodes)))
    coefs = []
    vs = []
    for n in range(0,nodes):
        vs += [toVar(n,c), toVar(n,c+1)]
        coefs += [str(-cf),str(cf)]
        cf //= 2
    assert(cf==1)
    solver.addConstraint(coefs,vs,True,"0",False,"")


# initialize the solver without an objective function
solver.init([], [], False, True)

if printNoSolve:
    solver.printFormula()
else:
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
