import cppyy
cppyy.include('/home/jod/workspace/exact-dev/src/Exact.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_debug/libexact')

import math

def addClause(lits):
    return cppyy.gbl.addConstraint(
        [int(math.copysign(1, l)) for l in lits],
        [str(abs(l)) for l in lits],
        True, 1-sum(1 for l in lits if l<0),
        False, 0)

addClause([1,2])
addClause([-1,-2])
addClause([-1,2])

print(cppyy.gbl.addConstraint([1,-1], ["1","2"], True, 0, False, 0))

cppyy.gbl.start()
