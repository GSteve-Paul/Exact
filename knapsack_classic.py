import cppyy
cppyy.include('/home/jod/workspace/exact-dev/src/Exact.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_lib/libExact')

import math
from cppyy.gbl import Exact

nvars = 50

var_range = range(1,nvars+1)

vars = [str(x) for x in var_range]
coefs_o = [5*x+(x%3) for x in var_range]
coefs_c = [5*x+(x%4) for x in var_range]
rhs_c = int(sum(coefs_c)*3/4)

exact = Exact()

for v in var_range:
     exact.addVariable(str(v),0,1+v%2)

print(exact.setObjective(coefs_o,vars))
print(exact.addConstraint(coefs_c, vars, True, rhs_c, False, 0))
exact.init(False)

exact.printFormula()

print("run:")
result = 1
while result!=0:
    result = exact.run()

sol = exact.getLastSolutionFor(vars)
print(result)
print(exact.getLowerBound())
print(exact.getUpperBound())
print(sum([sol[i]*coefs_o[i] for i in range(0,len(coefs_o))]))
print(sol)
