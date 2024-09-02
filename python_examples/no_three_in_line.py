# Problem: https://en.wikipedia.org/wiki/No-three-in-line_problem

# Import the exact package
import exact
import math
import sys

# Fixing Ramsey number instance
if len(sys.argv) not in [4, 5]:
    print("Usage: python3 no_three_in_line.py size points")
    print("Using default arguments: python3 no_three_in_line.py 5 10 29")
    size = 5  # size of the grid
    points = 10  # number of dots to put on the grid
    breakersize = 29  # size of symmetry breaking constraint
else:
    size = int(sys.argv[1])  # size of the grid
    points = int(sys.argv[2])  # number of dots to put on the grid
    breakersize = int(sys.argv[3])  # size of symmetry breaking constraint

printFormula = len(sys.argv) == 5

print("* Trying to put", points, "points on a", size, "by", size,
      "grid such that no three points are in the same line.", flush=True)

pairs = [[[[False for i in range(0, size)] for i in range(0, size)] for i in range(0, size)] for i in range(0, size)]
vars = [(i, j) for i in range(0, size) for j in range(0, size)]


# Calculate the diagonals

def getDiagonal(v1, v2):
    xdiff = v1[0] - v2[0]
    ydiff = v1[1] - v2[1]
    gcd = math.gcd(abs(xdiff), math.gcd(ydiff))
    xdiff //= gcd
    ydiff //= gcd
    res = [v1]
    v3 = v1
    while v3[0] >= 0 and v3[1] >= 0 and v3[0] < size and v3[1] < size:
        if v3 != v1:
            res += [v3]
        v3 = (v3[0] + xdiff, v3[1] + ydiff)
    v3 = v1
    while v3[0] >= 0 and v3[1] >= 0 and v3[0] < size and v3[1] < size:
        if v3 != v1:
            res += [v3]
        v3 = (v3[0] - xdiff, v3[1] - ydiff)
    return res


diagonals = []

for i in range(0, size * size):
    v1 = vars[i]
    for j in range(i + 1, size * size):
        v2 = vars[j]
        if pairs[v1[0]][v1[1]][v2[0]][v2[1]]:
            continue
        diag = getDiagonal(v1, v2)
        for v3 in diag:
            for v4 in diag:
                pairs[v3[0]][v3[1]][v4[0]][v4[1]] = True
        if len(diag) > 2:
            diagonals += [diag]

# Calculate the symmetries

s1 = size - 1
sym_x = [((i, j), (i, s1 - j)) for i in range(0, size) for j in range(0, size)]
sym_y = [((i, j), (s1 - i, j)) for i in range(0, size) for j in range(0, size)]
sym_d1 = [((i, j), (j, i)) for i in range(0, size) for j in range(0, size)]
sym_d2 = [((i, j), (s1 - j, s1 - i)) for i in range(0, size) for j in range(0, size)]
sym_r90 = [((i, j), (j, s1 - i)) for i in range(0, size) for j in range(0, size)]
sym_r180 = [((i, j), (s1 - i, s1 - j)) for i in range(0, size) for j in range(0, size)]
sym_r270 = [((i, j), (s1 - j, i)) for i in range(0, size) for j in range(0, size)]
symmetries = [sym_x, sym_y, sym_d1, sym_d2, sym_r90, sym_r180, sym_r270]

order = [(i, j) for i in range(0, size) for j in range(0, size)]
orderdict = {order[i]: i for i in range(0, len(order))}

shortenedSyms = []
for sym in symmetries:
    shortened = []
    for tup in sym:
        if len(shortened) >= breakersize:
            break
        if orderdict[tup[0]] >= orderdict[tup[1]]:
            continue
        shortened += [tup]
    if len(shortened) > 0:
        shortenedSyms += [shortened]

# Create an Exact solver instance
solver = exact.Exact()


# Add the variables
def to_var(v):
    return str(v[0]) + "_" + str(v[1])


variables = [to_var(v) for v in vars]

for v in vars:
    solver.addVariable(to_var(v))

# Add the constraints
for diag in diagonals:
    solver.addConstraint([(1, to_var(v)) for v in diag], False, 0, True, 2)

solver.addConstraint([(1, v) for v in variables], True, points, True, points)

for sym in shortenedSyms:
    terms = []
    cf = int(round(pow(2, len(sym))))
    for (v1, v2) in sym:
        terms += [(-cf, to_var(v1)), (cf, to_var(v2))]
        cf //= 2
    solver.addConstraint(terms, True, 0, False, 0)

if printFormula:
    solver.printFormula()
    exit(0)

# Run Exact
print("run Exact:")
state = solver.runFull(False)

print("RESULT:", state)
stats = dict(solver.getStats())
print("SEARCH CONFLICTS:", stats["conflicts"])

if solver.hasSolution():
    sol = solver.getLastSolutionFor(variables)
    for i in range(0, size):
        for j in range(0, size):
            index = i * size + j
            assert (to_var((i, j)) == variables[index])
            print("o" if sol[index] else ".", end='')
        print("")
