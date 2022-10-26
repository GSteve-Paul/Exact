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

# Problem: https://en.wikipedia.org/wiki/No-three-in-line_problem

import sys
import math

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Fixing Ramsey number instance
if len(sys.argv) != 3:
    print("Usage: python3 no_three_in_line.py size points")
    print("Using default arguments: python3 no_three_in_line.py 5 10")
    size = 5  # size of the grid
    points = 10  # number of dots to put on the grid
else:
    size = int(sys.argv[1])  # size of the grid
    points = int(sys.argv[2])  # number of dots to put on the grid

print("Trying to put",points,"points on a",size,"by",size,"grid such that no three points are in the same line.")

pairs = [[[[False for i in range(0,size)] for i in range(0,size)] for i in range(0,size)] for i in range(0,size)]
vars = [(i,j) for i in range(0,size) for j in range(0,size)]

diagonals = []

def getDiagonal(v1,v2):
    xdiff = v1[0]-v2[0]
    ydiff = v1[1]-v2[1]
    gcd = math.gcd(abs(xdiff), math.gcd(ydiff))
    xdiff //= gcd
    ydiff //= gcd
    res = [v1]
    v3 = v1
    while v3[0]>=0 and v3[1]>=0 and v3[0]<size and v3[1]<size:
        if v3!=v1:
            res += [v3]
        v3 = (v3[0]+xdiff,v3[1]+ydiff)
    v3 = v1
    while v3[0]>=0 and v3[1]>=0 and v3[0]<size and v3[1]<size:
        if v3!=v1:
            res += [v3]
        v3 = (v3[0]-xdiff,v3[1]-ydiff)
    return res


# Calculate the diagonals
for i in range(0,size*size):
    v1 = vars[i]
    for j in range(i+1,size*size):
        v2 = vars[j]
        if pairs[v1[0]][v1[1]][v2[0]][v2[1]]:
            continue
        diag = getDiagonal(v1,v2)
        for v3 in diag:
            for v4 in diag:
                pairs[v3[0]][v3[1]][v4[0]][v4[1]]=True
        if len(diag)>2:
            diagonals += [diag]

# Create an Exact solver instance
solver = exact.Exact()

# Add the variables
def to_var(v):
    return str(v[0]) + "_" + str(v[1])
variables = [to_var(v) for v in vars]

for v in vars:
    solver.addVariable(to_var(v), 0, 1)

# Add the constraints
for diag in diagonals:
    solver.addConstraint([1]*len(diag), [to_var(v) for v in diag], False, 0, True, 2)
solver.addConstraint([1]*len(variables),variables,True,points,True,points)

# Initialize Exact
solver.init([], [])

# solver.printFormula()

# Run Exact
print("run Exact:")
solver.runFull()

solver.printStats()

if solver.hasSolution():
    print("SAT")
    sol = solver.getLastSolutionFor(variables)
    print(variables)
    print(sol)
    for i in range(0,size):
        for j in range(0,size):
            index = i*size+j
            assert(to_var((i,j))==variables[index])
            print("o" if sol[index] else ".",end='')
        print("")
else:
    print("UNSAT")
