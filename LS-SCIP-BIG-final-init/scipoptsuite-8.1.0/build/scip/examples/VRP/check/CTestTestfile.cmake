# CMake generated Testfile for 
# Source directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check
# Build directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/scip/examples/VRP/check
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(examples-vrp-build "/usr/bin/cmake" "--build" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build" "--config" "Release" "--target" "vrp")
set_tests_properties(examples-vrp-build PROPERTIES  RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;18;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;0;")
add_test(examples-vrp-eil13 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/vrp" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/../data/eil13.vrp")
set_tests_properties(examples-vrp-eil13 PROPERTIES  DEPENDS "examples-vrp-build" RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;38;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;0;")
add_test(examples-vrp-eil7 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/vrp" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/../data/eil7.vrp")
set_tests_properties(examples-vrp-eil7 PROPERTIES  DEPENDS "examples-vrp-build" RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;38;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/VRP/check/CMakeLists.txt;0;")
