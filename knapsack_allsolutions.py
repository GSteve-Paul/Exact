import cppyy
cppyy.include('/home/jod/workspace/exact-dev/src/Exact.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_debug/libexact')

import math
from cppyy.gbl import Exact

nvars = 50

var_range = range(1,nvars+1)

vars = [str(x) for x in var_range]+["tmp"]
coefs_o = [5*x+(x%3) for x in var_range]+[1]
coefs_c = [5*x+(x%4) for x in var_range]
rhs_c = int(sum(coefs_c)*3/4)

exact = Exact()

def addClause(lits):
    return exact.addConstraint(
        [int(math.copysign(1, l)) for l in lits],
        [str(abs(l)) for l in lits],
        True, 1-sum(1 for l in lits if l<0),
        False, 0)

for v in var_range:
     exact.addVariable(str(v),0,1+v%2)
exact.addVariable("tmp",0,1)

print(exact.setObjective(coefs_o,vars))
print(exact.addConstraint(coefs_c, vars[:-1], True, rhs_c, False, 0))
exact.init(True)
exact.setAssumptions({"tmp"},{1})

exact.printFormula()

print("run:")
result = 1
while result!=0:
    result = exact.run()
    if result==1: # SAT
        assert(exact.hasSolution())
        # print(exact.getLastSolutionFor(vars))
        result = exact.addLastSolObjectiveBound()
        # result = exact.addLastSolInvalidatingClause()
    if result==2: # INCONSISTENT
        core = exact.getLastCore()
        assert(len(core)==1 and core[0] == "tmp")
        optVal = exact.getUpperBound()-1
        print("optimal:",optVal)
        exact.addConstraint(coefs_o, vars, True, optVal, True, optVal)
        exact.setAssumptions({},{})
        break

sol = exact.getLastSolutionFor(vars[:-1])
implied = {vars[i]:sol[i] for i in range(0,len(vars)-1)}

while result!=0:
    result = exact.run()
    if result==1:
        sol = exact.getLastSolutionFor(vars[:-1])
        implied = {vars[i]:sol[i] for i in range(0,len(vars)-1) if vars[i] in implied and implied[vars[i]]==sol[i]}
        result = exact.addLastSolInvalidatingClause()

print("Implied:",implied)
