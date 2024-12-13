if(NOT TARGET libzimpl)
  include("${CMAKE_CURRENT_LIST_DIR}/zimpl-targets.cmake")
endif()

set(ZIMPL_LIBRARIES libzimpl)
set(ZIMPL_PIC_LIBRARIES libzimpl-pic)
set(ZIMPL_INCLUDE_DIRS "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/zimpl/src")
set(ZIMPL_FOUND TRUE)

