import cppyy
cppyy.include('/home/jod/workspace/exact-dev/src/Exact.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_debug/libexact')

import math
from cppyy.gbl import Exact

nvars = 40

var_range = range(1,nvars+1)

vars = [str(x) for x in var_range]
coefs_o = [5*x+(x%3) for x in var_range]
coefs_c = [5*x+(x%4) for x in var_range]

exact = Exact()

def addClause(lits):
    return exact.addConstraint(
        [int(math.copysign(1, l)) for l in lits],
        [str(abs(l)) for l in lits],
        True, 1-sum(1 for l in lits if l<0),
        False, 0)

for v in var_range:
     exact.addVariable(str(v),0,1+v%2)

print(exact.setObjective(coefs_o,vars))
exact.init(False)
print(exact.addConstraint(coefs_c, vars, True, int(sum(coefs_c)/2), False, 0))

exact.printFormula()

print("run:")
result = 0
while result==0 or result==2:
    result = exact.run()

sol = exact.getLastSolutionFor(vars)
print(result)
print(exact.getLowerBound())
print(exact.getUpperBound())
print(sum([sol[i]*coefs_o[i] for i in range(0,len(coefs_o))]))
print(sol)
