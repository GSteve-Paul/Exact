# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION ${CMAKE_VERSION}) # this file comes with cmake

# If CMAKE_DISABLE_SOURCE_CHANGES is set to true and the source directory is an
# existing directory in our source tree, calling file(MAKE_DIRECTORY) on it
# would cause a fatal error, even though it would be a no-op.
if(NOT EXISTS "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-src")
  file(MAKE_DIRECTORY "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-src")
endif()
file(MAKE_DIRECTORY
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-build"
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix"
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/tmp"
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/src/tbb-populate-stamp"
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/src"
  "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/src/tbb-populate-stamp"
)

set(configSubDirs )
foreach(subDir IN LISTS configSubDirs)
    file(MAKE_DIRECTORY "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/src/tbb-populate-stamp/${subDir}")
endforeach()
if(cfgdir)
  file(MAKE_DIRECTORY "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-subbuild/tbb-populate-prefix/src/tbb-populate-stamp${cfgdir}") # cfgdir has leading slash
endif()
