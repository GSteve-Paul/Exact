# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION 3.31.2)

# Reject any attempt to use a toolchain file. We must not use one because
# we could be downloading it here. If the CMAKE_TOOLCHAIN_FILE environment
# variable is set, the cache variable will have been initialized from it.
unset(CMAKE_TOOLCHAIN_FILE CACHE)
unset(ENV{CMAKE_TOOLCHAIN_FILE})

# We name the project and the target for the ExternalProject_Add() call
# to something that will highlight to the user what we are working on if
# something goes wrong and an error message is produced.

project(tbb-populate NONE)



include(ExternalProject)
ExternalProject_Add(tbb-populate
                     "UPDATE_DISCONNECTED" "False" "DOWNLOAD_EXTRACT_TIMESTAMP" "TRUE" "EXTERNALPROJECT_INTERNAL_ARGUMENT_SEPARATOR" "URL" "https://github.com/oneapi-src/oneTBB/archive/refs/tags/v2021.4.0.tar.gz" "URL_HASH" "SHA256=021796c7845e155e616f5ecda16daa606ebb4c6f90b996e5c08aebab7a8d3de3"
                    SOURCE_DIR          "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-src"
                    BINARY_DIR          "/home/lijn/research/Exact/LS-SCIP-BIG-final-init/scipoptsuite-8.1.0/_deps/tbb-build"
                    CONFIGURE_COMMAND   ""
                    BUILD_COMMAND       ""
                    INSTALL_COMMAND     ""
                    TEST_COMMAND        ""
                    USES_TERMINAL_DOWNLOAD  YES
                    USES_TERMINAL_UPDATE    YES
                    USES_TERMINAL_PATCH     YES
)


