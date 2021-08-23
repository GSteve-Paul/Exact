import exact

import math

nvars = 50

var_range = range(1,nvars+1)

vars = [str(x) for x in var_range]
coefs_o = [5*x+(x%3) for x in var_range]
coefs_c = [5*x+(x%4) for x in var_range]
rhs_c = int(sum(coefs_c)*3/4)

solver = exact.solver()

for v in var_range:
     solver.addVariable(str(v),0,1+v%2)

print(solver.addConstraint(coefs_c, vars, True, rhs_c, False, 0))
solver.init(coefs_o, vars, True, True)

solver.printFormula()

print("run:")
result = 1
while result!=0:
    result = solver.run()

sol = solver.getLastSolutionFor(vars)
print(result)
print(list(solver.getObjectiveBounds()))
print(sum([sol[i]*coefs_o[i] for i in range(0,len(coefs_o))]))
print(sol)
