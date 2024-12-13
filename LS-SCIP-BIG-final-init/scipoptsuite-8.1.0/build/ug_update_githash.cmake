
find_program(GIT git)
if(EXISTS ${DST})
   file(STRINGS ${DST} GITHASH_OLD)
   string(REGEX REPLACE "#define UG_GITHASH \"(.*)\"" "\\1" GITHASH_OLD ${GITHASH_OLD})
endif()
if((GIT) AND (EXISTS /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/ug/.git))
   execute_process(
      COMMAND ${GIT} describe --always --dirty
      WORKING_DIRECTORY /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/ug
      OUTPUT_VARIABLE GITHASH OUTPUT_STRIP_TRAILING_WHITESPACE)
   string(REGEX REPLACE "^.*-g" "" GITHASH ${GITHASH})
   if(NOT ${GITHASH} STREQUAL "${GITHASH_OLD}")
      file(WRITE ${DST} "#define UG_GITHASH \"${GITHASH}\"
")
   endif()
else()
   set(GITHASH ${GITHASH_OLD})
   if(NOT GITHASH)
      message(STATUS "Compiling without git information")
      set(GITHASH "NoGitInfo")
   endif()
   file(WRITE ${DST} "#define UG_GITHASH \"${GITHASH}\"
")
endif()
message(STATUS "Git hash: " ${GITHASH})
