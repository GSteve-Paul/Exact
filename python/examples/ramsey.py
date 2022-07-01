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

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Create an Exact solver instance
solver = exact.Exact()

# Fixing Ramsey number instance
nodes = 24 # size of the graph
cliques = [4,5]  # size of cliques

def toVar(v1,v2):
    return str(v1)+"_"+str(v2);

edges = [toVar(i,j) for i in range(0,nodes) for j in range(i+1,nodes)]

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
        vars = [toVar(clique[i],clique[j]) for i in range(0,n) for j in range(i+1,n)]
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
def swapif(v,i,j):
    return j if v==i else i if v==j else v
def image(v1,v2,i,j):
    i1 = swapif(v1,i,j)
    i2 = swapif(v2,i,j)
    return (i1,i2) if i1 <= i2 else (i2,i1)

cutoff = 60 # should be less than 64 so that resulting coefficients still fit in long long
order = [(i,j) for i in range(0,nodes) for j in range(i+1,nodes)]
orderdict = {order[i]:i for i in range(0,len(order))}
for i in range(0,nodes):
    for j in range(i+1,nodes):
        images = []
        for (v1,v2) in order:
            (v3,v4) = image(v1,v2,i,j)
            if (v1!=v3 or v2!=v4) and orderdict[(v1,v2)]<orderdict[(v3,v4)]:
                images += [(v1,v2,v3,v4)]
                if len(images)>=cutoff:
                    break
        coefs = []
        vars = []
        c = int(round(pow(2,len(images))))
        for (v1,v2,v3,v4) in images:
            vars += [toVar(v1,v2), toVar(v3,v4)]
            coefs += [-c,c]
            c //= 2
        solver.addConstraint(coefs, vars, True, 0, False, 0)

# Symmetry breaking on color
if cliques[0]==cliques[1]:
    solver.addConstraint([1], [toVar(order[0][0],order[0][1])], False, 0, True, 0)

# Initialize Exact
solver.init([], [], False, True)

# solver.printFormula()

# Run Exact
print("run Exact:")
result = 3
while result>1:
     # As long as the result is not UNSAT (== 0), the solver is kept running.
     result = solver.run()

if result==0:
    assert not solver.hasSolution()
    print("UNSAT")
else:
    assert solver.hasSolution()
    print("SAT")
    sol = solver.getLastSolutionFor(edges)
    print(sol)
