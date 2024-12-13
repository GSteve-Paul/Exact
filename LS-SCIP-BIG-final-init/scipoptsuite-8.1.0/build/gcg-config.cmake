if(NOT TARGET libgcg)
  include("${CMAKE_CURRENT_LIST_DIR}/gcg-targets.cmake")
endif()

if(1)
   set(SCIP_DIR "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/scip")
   find_package(SCIP QUIET CONFIG)
endif()

set(GCG_LIBRARIES libgcg)
set(GCG_INCLUDE_DIRS "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src")
set(GCG_FOUND TRUE)
