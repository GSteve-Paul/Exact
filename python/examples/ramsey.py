# This file is part of Exact.
#
# Copyright (c) 2022 Jo Devriendt
#
# Exact is free software: you can redistribute it and/or modify it under
# the terms of the GNU Affero General Public License version 3 as
# published by the Free Software Foundation.
#
# Exact is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public
# License version 3 for more details.
#
# You should have received a copy of the GNU Affero General Public
# License version 3 along with Exact. See the file used_licenses/COPYING
# or run with the flag --license=AGPLv3. If not, see
# <https://www.gnu.org/licenses/>.

# Looking for Ramsey numbers

import math
import sys

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

solver.setOption("var-weight","0")

# Fixing Ramsey number instance
if len(sys.argv)!=6:
    print("Usage: python3 ramsey.py #nodes cliquesize1 cliquesize2 symcutoff count-breakers")
    exit(1)
nodes = int(sys.argv[1]) # size of the graph
cliques = [int(sys.argv[2]),int(sys.argv[3])]  # size of cliques
cutoff = int(sys.argv[4]) # should be less than 64 so that resulting coefficients still fit in long long
uselex = int(sys.argv[5])<2
usecounting = int(sys.argv[5])>0
print("Searching for complete bicolored graph with",nodes,"nodes and no blue cliques of size",cliques[0],"and no red cliques of size",cliques[1])
if uselex:
    print("Lex-leader symmetry breaker cutoff:",cutoff)
if usecounting:
    print("Using counting symmetry breaking")

def normalize(v):
    return v if v[0]<=v[1] else (v[1],v[0])
def toVar(v):
    vv = normalize(v)
    return str(vv[0])+"_"+str(vv[1]);

edges = [toVar((i,j)) for i in range(0,nodes) for j in range(i+1,nodes)]

# Add the variables
for e in edges:
    solver.addVariable(e,0,1)

# Add the Ramsey constraints
flag = True
for n in cliques:
    clique = list(range(0,n))
    edgesize = ((n*(n-1))//2)
    coefs = [1]*edgesize

    while True:
        vars = [toVar((clique[i],clique[j])) for i in range(0,n) for j in range(i+1,n)]
        solver.addConstraint(coefs, vars, not flag, 1, flag, edgesize-1)
        index = n-1
        clique[index] += 1
        while index >= 0 and clique[index] >= nodes+index-n+1:
            clique[index] = 0
            index -= 1
            clique[index] += 1
        if index<0:
            break
        for i in range(1,n):
            if clique[i] <= clique[i-1]:
                clique[i] = clique[i-1]+1

    flag = False

# Lex-leader symmetry breaking
def swapif(v,swap):
    return swap[1] if v==swap[0] else swap[0] if v==swap[1] else v
def image(v,swap):
    return normalize((swapif(v[0],swap),swapif(v[1],swap)))

order = [(i,j) for i in range(0,nodes) for j in range(i+1,nodes)]
orderdict = {order[i]:i for i in range(0,len(order))}
def addLexLeader(swap1,swap2):
    images = []
    for (v1,v2) in order:
        (v3,v4) = image(image((v1,v2),swap1),swap2)
        if (v1!=v3 or v2!=v4) and orderdict[(v1,v2)]<orderdict[(v3,v4)]:
            images += [((v1,v2),(v3,v4))]
            if len(images)>=cutoff:
                break
    coefs = []
    vars = []
    c = int(round(pow(2,len(images))))
    for (v1,v2) in images:
        vars += [toVar(v1), toVar(v2)]
        coefs += [-c,c]
        c //= 2
    solver.addConstraint(coefs, vars, True, 0, False, 0)

if uselex:
    for i in range(0,nodes):
        print(i)
        for j in range(i+1,nodes):
            addLexLeader((i,j),(0,0)) # swap only i and j
            for k in range(i+1,nodes):
                for l in range(k+1,nodes):
                    addLexLeader((i,j),(k,l))
if usecounting:
    for i in range(0,nodes-1):
        vars=[toVar((i,j)) for j in range(0,nodes) if j!=i]+[toVar((i+1,j)) for j in range(0,nodes) if j!=i+1]
        coefs=([-1]*(nodes-1)) + ([1]*(nodes-1))
        solver.addConstraint(coefs, vars, True, 0, False, 0)

# Symmetry breaking on color
if cliques[0]==cliques[1]:
    solver.addConstraint([1], [toVar(order[0])], False, 0, True, 0)

# Initialize Exact
solver.init([], [], False, True)

# solver.printFormula()

# Run Exact
print("run Exact:")
result = 3
while result>1:
     # As long as the result is not UNSAT (== 0), the solver is kept running.
     result = solver.run()

solver.printStats()

if result==0:
    assert not solver.hasSolution()
    print("UNSAT")
else:
    assert solver.hasSolution()
    print("SAT")
    sol = solver.getLastSolutionFor(edges)
    print(sol)
