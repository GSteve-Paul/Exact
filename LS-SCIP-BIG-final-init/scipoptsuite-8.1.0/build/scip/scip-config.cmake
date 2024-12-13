if(NOT TARGET libscip)
  include("${CMAKE_CURRENT_LIST_DIR}/scip-targets.cmake")
endif()

if()
   set(ZIMPL_DIR "")
   find_package(ZIMPL QUIET CONFIG)
endif()

if(1)
   set(SOPLEX_DIR "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build")
   find_package(SOPLEX QUIET CONFIG)
endif()

set(SCIP_LIBRARIES libscip)
set(SCIP_INCLUDE_DIRS "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/src;/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/scip")
set(SCIP_FOUND TRUE)
