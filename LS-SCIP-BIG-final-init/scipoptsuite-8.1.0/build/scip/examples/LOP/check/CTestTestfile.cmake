# CMake generated Testfile for 
# Source directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check
# Build directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/scip/examples/LOP/check
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(examples-lop-build "/usr/bin/cmake" "--build" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build" "--config" "Release" "--target" "lop")
set_tests_properties(examples-lop-build PROPERTIES  RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;19;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;0;")
add_test(examples-lop-ex1 "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/lop" "-f" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/../data/ex1.lop" "-o" "3100" "3100")
set_tests_properties(examples-lop-ex1 PROPERTIES  DEPENDS "examples-lop-build" PASS_REGULAR_EXPRESSION "Validation         : Success" RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;41;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;0;")
add_test(examples-lop-t65i11xx "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/lop" "-f" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/../data/t65i11xx.lop" "-o" "16389651" "16389651")
set_tests_properties(examples-lop-t65i11xx PROPERTIES  DEPENDS "examples-lop-build" PASS_REGULAR_EXPRESSION "Validation         : Success" RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;41;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;0;")
add_test(examples-lop-t70x11xx "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/examples/lop" "-f" "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/../data/t70x11xx.lop" "-o" "343471236" "343471236")
set_tests_properties(examples-lop-t70x11xx PROPERTIES  DEPENDS "examples-lop-build" PASS_REGULAR_EXPRESSION "Validation         : Success" RESOURCE_LOCK "libscip" _BACKTRACE_TRIPLES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;41;add_test;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/examples/LOP/check/CMakeLists.txt;0;")
