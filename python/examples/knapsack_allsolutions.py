import exact

import math

nvars = 50

var_range = range(1,nvars+1)

vars = [str(x) for x in var_range]+["tmp"]
coefs_o = [5*x+(x%3) for x in var_range]+[1]
coefs_c = [5*x+(x%4) for x in var_range]
rhs_c = int(sum(coefs_c)*3/4)

solver = exact.solver()

def addClause(lits):
    return solver.addConstraint(
        [int(math.copysign(1, l)) for l in lits],
        [str(abs(l)) for l in lits],
        True, 1-sum(1 for l in lits if l<0),
        False, 0)

for v in var_range:
    solver.addVariable(str(v),0,1+v%2)
solver.addVariable("tmp",0,1)

print(solver.setObjective(coefs_o,vars))
print(solver.addConstraint(coefs_c, vars[:-1], True, rhs_c, False, 0))
solver.init(True)
solver.setAssumptions({"tmp"},{1})

solver.printFormula()

print("run:")
result = 1
while result!=0:
    result = solver.run()
    if result==1: # SAT
        assert(solver.hasSolution())
        # print(solver.getLastSolutionFor(vars))
        result = solver.addLastSolObjectiveBound()
        # result = solver.addLastSolInvalidatingClause()
    if result==2: # INCONSISTENT
        core = solver.getLastCore()
        assert(len(core)==1 and core[0] == "tmp")
        optVal = solver.getUpperBound()-1
        print("optimal:",optVal)
        solver.addConstraint(coefs_o, vars, True, optVal, True, optVal)
        solver.setAssumptions({},{})
        break

sol = solver.getLastSolutionFor(vars[:-1])
implied = {vars[i]:sol[i] for i in range(0,len(vars)-1)}

while result!=0:
    result = solver.run()
    if result==1:
        sol = solver.getLastSolutionFor(vars[:-1])
        implied = {vars[i]:sol[i] for i in range(0,len(vars)-1) if vars[i] in implied and implied[vars[i]]==sol[i]}
        result = solver.addLastSolInvalidatingClause()

print("Implied:",implied)
