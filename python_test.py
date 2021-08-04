import cppyy

cppyy.include('/home/jod/workspace/exact-dev/src/Exact.hpp')
cppyy.load_library('/home/jod/workspace/exact-dev/build_debug/libexact')

cppyy.gbl.addClause({1,2})

cppyy.gbl.start()
