# Install script for directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/papilo/CMakeConfig.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/Config.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo-config-version.cmake")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/core" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Components.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/ConstraintMatrix.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/MatrixBuffer.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Objective.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Presolve.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/PresolveMethod.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/PresolveOptions.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/ProbingView.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Problem.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/ProblemBuilder.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/ProblemUpdate.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Reductions.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/RowFlags.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/SingleRow.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Solution.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/SparseStorage.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/Statistics.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/VariableDomains.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/core/postsolve" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/BoundStorage.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/PostsolveStorage.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/Postsolve.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/PostsolveStatus.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/PostsolveType.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/ReductionType.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/core/postsolve/SavedRow.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/interfaces" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/HighsInterface.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/GlopInterface.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/GurobiInterface.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/ScipInterface.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/SolverInterface.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/interfaces/SoplexInterface.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/io" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/io/Message.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/io/MpsParser.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/io/MpsWriter.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/io/SolParser.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/io/SolWriter.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/misc" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Alloc.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Array.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/compress_vector.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/DependentRows.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Flags.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/fmt.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Hash.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/MultiPrecision.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Num.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/NumericalStatistics.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/PrimalDualSolValidation.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/OptionsParser.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/VersionLogger.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/ParameterSet.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Signature.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/StableSum.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/String.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/tbb.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Timer.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Validation.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Vec.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/VectorUtils.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/Wrappers.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/misc" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/misc/extended_euclidean.hpp")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/presolvers" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/CoefficientStrengthening.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/ConstraintPropagation.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/DominatedCols.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/DualFix.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/DualInfer.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/FixContinuous.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/FreeVarSubstitution.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/ImplIntDetection.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/ParallelColDetection.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/ParallelRowDetection.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/Probing.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/SimpleProbing.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/SimpleSubstitution.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/SimplifyInequalities.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/SingletonCols.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/SingletonStuffing.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/presolvers/Sparsify.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/external/fmt" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/chrono.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/color.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/compile.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/core.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/format.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/format-inl.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/locale.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/ostream.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/posix.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/printf.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/ranges.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/format.cc"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/fmt/posix.cc"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/external/pdqsort" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/pdqsort/pdqsort.h")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/external/ska" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/ska/bytell_hash_map.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/ska/flat_hash_map.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/ska/unordered_map.hpp"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/papilo/external/lusol" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/src/papilo/external/lusol/clusol.h")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/cmake/Modules/FindQuadmath.cmake")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/CMakeFiles/papilo-config.cmake")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/papilo/cmake/Modules/FindTBB.cmake")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/libpapilo-core.a")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo/papilo-targets.cmake")
    file(DIFFERENT EXPORT_FILE_CHANGED FILES
         "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo/papilo-targets.cmake"
         "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/CMakeFiles/Export/lib/cmake/papilo/papilo-targets.cmake")
    if(EXPORT_FILE_CHANGED)
      file(GLOB OLD_CONFIG_FILES "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo/papilo-targets-*.cmake")
      if(OLD_CONFIG_FILES)
        message(STATUS "Old export file \"$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo/papilo-targets.cmake\" will be replaced.  Removing files [${OLD_CONFIG_FILES}].")
        file(REMOVE ${OLD_CONFIG_FILES})
      endif()
    endif()
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/CMakeFiles/Export/lib/cmake/papilo/papilo-targets.cmake")
  if("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/papilo" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/CMakeFiles/Export/lib/cmake/papilo/papilo-targets-release.cmake")
  endif()
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/papilo/test/cmake_install.cmake")

endif()

