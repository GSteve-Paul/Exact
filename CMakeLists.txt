cmake_minimum_required(VERSION 3.5)
project(Exact)

set(CMAKE_CXX_STANDARD 17)
# Feel free to decrease the required boost version if you can verify that it works with
# a smaller version. It is known not to compile with version 1.53.0 and lower.
find_package(Boost 1.67 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")

set(CMAKE_CXX_FLAGS_TESTRUNS "-O3")

if (NOT CMAKE_BUILD_TYPE)
    message(WARNING "Please use -DCMAKE_BUILD_TYPE=[build_type] where [build_type] is one of: Debug, Release, RelWithDebInfo, MinSizeRel, TestRuns")
endif()

set(build_static "OFF"
    CACHE STRING "Build and use static libraries.")

set(profile_flags "OFF"
    CACHE STRING "Build using gprof flag (-pg).")

set(soplex "OFF"
    CACHE STRING "Use SoPlex to check for rational infeasibility.")

set(soplex_pkg "${PROJECT_SOURCE_DIR}/soplex-5.0.2.tgz"
    CACHE STRING "SoPlex package, download at https://soplex.zib.de/download.php?fname=soplex-5.0.2.tgz")

set(coinutils "OFF"
    CACHE STRING "Coin OR Utils library to parse .mps and .lp files.")

set(testruns_timeout 1
    CACHE STRING "Timeout of individual test runs.")

IF(soplex)
    # provides libsoplex and ${SOPLEX_INCLUDE_DIRS}
    include(${PROJECT_SOURCE_DIR}/cmake/soplex_build_and_load.cmake)
endif()

if(coinutils)
    find_package(CoinUtils REQUIRED)
    include_directories(${CoinUtils_INCLUDE_DIR})
endif()

if(${build_static})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libgcc -static-libstdc++ -static")
endif()

if(${profile_flags})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")
endif()

# Get the current working branch
execute_process(
    COMMAND git rev-parse --abbrev-ref HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_BRANCH
    OUTPUT_STRIP_TRAILING_WHITESPACE
)
# Get the latest abbreviated commit hash of the working branch
execute_process(
    COMMAND git log -1 --format=%h
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE
)
add_definitions("-DGIT_COMMIT_HASH=${GIT_COMMIT_HASH}")
add_definitions("-DGIT_BRANCH=${GIT_BRANCH}")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

set(source_files
    src/globals.cpp
    src/Constr.cpp
    src/ConstrExp.cpp
    src/ConstrSimple.cpp
    src/ConstrExpPools.cpp
    src/LpSolver.cpp
    src/IntSet.cpp
    src/Solver.cpp
    src/SolverStructs.cpp
    src/parsing.cpp
    src/quit.cpp
    src/Exact.cpp
    src/run.cpp
    src/Heuristic.cpp
    src/aux.cpp

    src/used_licenses/licenses.cpp
    src/used_licenses/zib_academic.cpp
    src/used_licenses/roundingsat.cpp
    src/used_licenses/MIT.cpp
    src/used_licenses/boost.cpp
    src/used_licenses/EPL.cpp
)

set(header_files
    src/globals.hpp
    src/Constr.hpp
    src/ConstrExp.hpp
    src/ConstrSimple.hpp
    src/SolverStructs.hpp
    src/ConstrExpPools.hpp
    src/Logger.hpp
    src/Stats.hpp
    src/LpSolver.hpp
    src/Options.hpp
    src/IntSet.hpp
    src/Solver.hpp
    src/typedefs.hpp
    src/aux.hpp
    src/parsing.hpp
    src/quit.hpp
    src/run.hpp
    src/Heuristic.hpp

    src/used_licenses/licenses.hpp
    src/used_licenses/zib_academic.hpp
    src/used_licenses/roundingsat.hpp
    src/used_licenses/MIT.hpp
    src/used_licenses/boost.hpp
    src/used_licenses/EPL.hpp
)

set(all_files ${source_files} ${header_files})

add_executable(Exact ${source_files})
target_include_directories(Exact PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})
install(TARGETS Exact RUNTIME DESTINATION bin)

if(soplex)
    target_link_libraries(Exact libsoplex)
    target_compile_definitions(Exact PUBLIC WITHSOPLEX)
endif()

if(coinutils)
    target_link_libraries(Exact CoinUtils z bz2)
    target_compile_definitions(Exact PUBLIC WITHCOINUTILS)
endif()

FIND_PROGRAM(CLANG_FORMAT "clang-format")
IF(CLANG_FORMAT)
    add_custom_target(
        format
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        COMMAND ${CLANG_FORMAT}
        -style=file
        -i
        ${all_files}
    )
endif()

add_custom_target(
    testruns
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/test
    COMMAND ./run_tests.sh ${testruns_timeout} "testruns" ${CMAKE_CURRENT_BINARY_DIR}/Exact
)
add_dependencies(testruns Exact)
