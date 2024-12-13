# CMake generated Testfile for 
# Source directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens
# Build directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/scip/examples/Queens
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(examples-queens-build "/usr/bin/cmake" "--build" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build" "--config" "Release" "--target" "queens")
set_tests_properties(examples-queens-build PROPERTIES  RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;28;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
add_test(examples-queens-1 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/queens" "1")
set_tests_properties(examples-queens-1 PROPERTIES  DEPENDS "examples-queens-build" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;52;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
add_test(examples-queens-2 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/queens" "2")
set_tests_properties(examples-queens-2 PROPERTIES  DEPENDS "examples-queens-build" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;52;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
add_test(examples-queens-4 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/queens" "4")
set_tests_properties(examples-queens-4 PROPERTIES  DEPENDS "examples-queens-build" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;52;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
add_test(examples-queens-8 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/queens" "8")
set_tests_properties(examples-queens-8 PROPERTIES  DEPENDS "examples-queens-build" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;52;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
add_test(examples-queens-16 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/queens" "16")
set_tests_properties(examples-queens-16 PROPERTIES  DEPENDS "examples-queens-build" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;52;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/Queens/CMakeLists.txt;0;")
