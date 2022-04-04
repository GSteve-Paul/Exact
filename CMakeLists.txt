cmake_minimum_required(VERSION 3.5)
project(Exact)

set(CMAKE_CXX_STANDARD 17)

# include_directories("src" ) # NOTE: don't include non-standard directories, as cppyy complains about those

# Feel free to decrease the required boost version if you can verify that it works with
# a smaller version. It is known not to compile with version 1.53.0 and lower.
find_package(Boost 1.67 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")

set(CMAKE_CXX_FLAGS_TESTRUNS "-O3")

if (NOT CMAKE_BUILD_TYPE)
    message(WARNING "Please use -DCMAKE_BUILD_TYPE=[Debug | Release | RelWithDebInfo | MinSizeRel | TestRuns]")
endif()

set(build_result "Executable"
    CACHE STRING "Result of make command: Executable, SharedLib or StaticLib.")

if (NOT (build_result STREQUAL "Executable" OR build_result STREQUAL "SharedLib" OR build_result STREQUAL "StaticLib"))
    message(WARNING "Please use -Dbuild_result=[Executable | SharedLib | StaticLib]")
endif()

set(build_static "OFF"
    CACHE STRING "Build statically linked executable.")

set(profile_flags "OFF"
    CACHE STRING "Build using gprof flag (-pg).")

set(soplex "OFF"
    CACHE STRING "Use SoPlex to check for rational infeasibility.")

set(soplex_pkg "${PROJECT_SOURCE_DIR}/soplex-6.0.0.tgz"
    CACHE STRING "SoPlex zip package, available at https://soplex.zib.de/download.php?fname=soplex-6.0.0.tgz")

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

if(build_static)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libgcc -static-libstdc++ -static")
endif()

if(profile_flags)
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
        src/constraints/Constr.cpp
        src/constraints/ConstrExp.cpp
        src/constraints/ConstrSimple.cpp
        src/constraints/ConstrExpPools.cpp
        src/propagation/LpSolver.cpp
        src/Solver.cpp
        src/ILP.cpp
        src/datastructures/SolverStructs.cpp
        src/Logger.cpp
        src/datastructures/IntSet.cpp
        src/parsing.cpp
        src/datastructures/Heuristic.cpp
        src/auxiliary.cpp
        src/Optimization.cpp
        src/quit.cpp
        src/Exact.cpp
        src/propagation/Propagator.cpp
        src/propagation/Equalities.cpp
        src/propagation/Implications.cpp

        src/used_licenses/licenses.cpp
        src/used_licenses/zib_academic.cpp
        src/used_licenses/roundingsat.cpp
        src/used_licenses/MIT.cpp
        src/used_licenses/boost.cpp
        src/used_licenses/EPL.cpp
        src/used_licenses/COPYING.cpp
)

set(header_files
        src/globals.hpp
        src/constraints/Constr.hpp
        src/constraints/ConstrExp.hpp
        src/constraints/ConstrSimple.hpp
        src/datastructures/SolverStructs.hpp
        src/constraints/ConstrExpPools.hpp
        src/propagation/LpSolver.hpp
        src/Solver.hpp
        src/ILP.hpp
        src/Logger.hpp
        src/datastructures/IntMap.hpp
        src/datastructures/IntSet.hpp
        src/typedefs.hpp
        src/parsing.hpp
        src/datastructures/Heuristic.hpp
        src/Stats.hpp
        src/Options.hpp
        src/auxiliary.hpp
        src/quit.hpp
        src/Optimization.hpp
        src/propagation/Propagator.hpp
        src/propagation/Equalities.hpp
        src/propagation/Implications.hpp
        src/Exact.hpp

        src/used_licenses/licenses.hpp
        src/used_licenses/zib_academic.hpp
        src/used_licenses/roundingsat.hpp
        src/used_licenses/MIT.hpp
        src/used_licenses/boost.hpp
        src/used_licenses/EPL.hpp
        src/used_licenses/COPYING.hpp
)

set(all_files ${source_files} ${header_files})

if(build_result STREQUAL "Executable")
    add_executable(Exact ${source_files})

    if(soplex)
        target_link_libraries(Exact libsoplex)
        target_compile_definitions(Exact PUBLIC WITHSOPLEX)
    endif()

    if(coinutils)
        target_link_libraries(Exact CoinUtils z bz2)
        target_compile_definitions(Exact PUBLIC WITHCOINUTILS)
    endif()

    target_include_directories(Exact PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})
    install(TARGETS Exact RUNTIME DESTINATION bin)

    add_custom_target(
            testruns
            WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/test
            COMMAND ./run_tests.sh ${testruns_timeout} "testruns" ${CMAKE_CURRENT_BINARY_DIR}/Exact
    )
    add_dependencies(testruns Exact)
endif()

if(build_result STREQUAL "SharedLib")
    add_library(Exact SHARED ${source_files})

    if(soplex)
        target_link_libraries(Exact libsoplex)
        target_compile_definitions(Exact PUBLIC WITHSOPLEX)
    endif()

    target_include_directories(Exact PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})
    set_target_properties(Exact PROPERTIES PUBLIC_HEADER src/Exact.hpp)
endif()

if(build_result STREQUAL "StaticLib")
    add_library(Exact STATIC ${source_files})

    if(soplex)
        target_link_libraries(Exact libsoplex)
        target_compile_definitions(Exact PUBLIC WITHSOPLEX)
    endif()

    target_include_directories(Exact PRIVATE ${PROJECT_SOURCE_DIR}/src/ ${SOPLEX_INCLUDE_DIRS})
    set_target_properties(Exact PROPERTIES PUBLIC_HEADER src/Exact.hpp)
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
