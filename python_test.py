import cppyy
cppyy.include('/home/jod/workspace/exact-dev/src/PublicInterface.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_debug/libexact')

import math
from cppyy.gbl import Exact

exact = Exact()

def addClause(lits):
    return exact.addConstraint(
        [int(math.copysign(1, l)) for l in lits],
        [str(abs(l)) for l in lits],
        True, 1-sum(1 for l in lits if l<0),
        False, 0)

print(addClause([1,2]))
print(exact.setObjective([1,2],["1","2"]))
exact.init()
print(exact.addConstraint([-1,-1], ["1","2"], True, -1, False, 0))

print("run:")
print(exact.run())
