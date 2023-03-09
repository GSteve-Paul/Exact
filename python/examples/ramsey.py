# Looking for Ramsey numbers (https://en.wikipedia.org/wiki/Ramsey%27s_theorem)

import sys

# Import the exact package, e.g., from PyPI using poetry or pip
import exact

# Fixing Ramsey number instance
if len(sys.argv) != 6:
    print("Usage: python3 ramsey.py #nodes cliquesize1 cliquesize2 symcutoff count-breakers")
    print("Using default arguments: python3 ramsey.py 9 3 4 29 0")
    nodes = 17  # size of the graph
    cliques = [4,4]  # size of cliques
    cutoff = 29  # should be less than 64 so that resulting coefficients still fit in long long
    uselex = True
    usecounting = False
else:
    nodes = int(sys.argv[1])  # size of the graph
    cliques = [int(sys.argv[2]), int(sys.argv[3])]  # size of cliques
    cutoff = int(sys.argv[4])  # should be less than 64 so that resulting coefficients still fit in long long
    uselex = int(sys.argv[5]) < 2
    usecounting = int(sys.argv[5]) > 0
print("Searching for complete bicolored graph with", nodes, "nodes and no blue cliques of size", cliques[0],
      "and no red cliques of size", cliques[1])
if uselex:
    print("Lex-leader symmetry breaker cutoff:", cutoff)
if usecounting:
    print("Using counting symmetry breaking")

def normalize(v):
    return v if v[0] <= v[1] else (v[1], v[0])

def to_var(v):
    vv = normalize(v)
    return str(vv[0]) + "_" + str(vv[1])

variables = [to_var((i, j)) for i in range(0, nodes) for j in range(i + 1, nodes)]
constraints = []

# Add the Ramsey constraints
flag = True
for n in cliques:
    clique = list(range(0, n))
    edgesize = ((n * (n - 1)) // 2)
    coefs = [1] * edgesize

    while True:
        vs = [to_var((clique[i], clique[j])) for i in range(0, n) for j in range(i + 1, n)]
        constraints += [(coefs, vs, not flag, 1, flag, edgesize - 1)]
        index = n - 1
        clique[index] += 1
        while index >= 0 and clique[index] >= nodes + index - n + 1:
            clique[index] = 0
            index -= 1
            clique[index] += 1
        if index < 0:
            break
        for i in range(1, n):
            if clique[i] <= clique[i - 1]:
                clique[i] = clique[i - 1] + 1
    flag = False


# Lex-leader symmetry breaking
def swapif(v, swap):
    return swap[1] if v == swap[0] else swap[0] if v == swap[1] else v
def image(v, swap):
    return normalize((swapif(v[0], swap), swapif(v[1], swap)))

order = [(i, j) for i in range(0, nodes) for j in range(i + 1, nodes)]
orderdict = {order[i]: i for i in range(0, len(order))}


def get_lex_leader(swap1, swap2):
    images = []
    for (v1, v2) in order:
        (v3, v4) = image(image((v1, v2), swap1), swap2)
        if (v1 != v3 or v2 != v4) and orderdict[(v1, v2)] < orderdict[(v3, v4)]:
            images += [((v1, v2), (v3, v4))]
            if len(images) >= cutoff:
                break
    cfs = []
    vs = []
    cf = int(round(pow(2, len(images))))
    for (v1, v2) in images:
        vs += [to_var(v1), to_var(v2)]
        cfs += [-cf, cf]
        cf //= 2
    return cfs, vs, True, 0, False, 0


if uselex:
    for i in range(0, nodes):
        print(i)
        for j in range(i + 1, nodes):
            constraints += [get_lex_leader((i, j), (0, 0))]  # swap only i and j
            for k in range(i + 1, nodes):
                for l in range(k + 1, nodes):
                    constraints += [get_lex_leader((i, j), (k, l))]
if usecounting:
    for i in range(0, nodes - 1):
        vs = [to_var((i, j)) for j in range(0, nodes) if j != i] + \
             [to_var((i + 1, j)) for j in range(0, nodes) if j != i + 1]
        coefs = ([-1] * (nodes - 1)) + ([1] * (nodes - 1))
        constraints += [(coefs, vs, True, 0, False, 0)]

# Symmetry breaking on color
if cliques[0] == cliques[1]:
    constraints += [([1], [to_var(order[0])], False, 0, True, 0)]


# Create an Exact solver instance
solver = exact.Exact()

# Add the variables
for e in variables:
    solver.addVariable(e, 0, 1)
# Add the constraints
for (coefs, vs, uselow, low, useup, up) in constraints:
    solver.addConstraint(coefs, vs, uselow, low, useup, up)

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
    print(sol)
else:
    print("UNSAT")

