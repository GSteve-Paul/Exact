cmake_minimum_required(VERSION 3.10)
project(DNOP)

set(CMAKE_CXX_STANDARD 17)
get_property(languages GLOBAL PROPERTY ENABLED_LANGUAGES)
message(STATUS "languages: ${languages}")

# 查找 TBB
#message(${CMAKE_CURRENT_SOURCE_DIR}/../oneTBB/build)
#set(TBB_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../oneTBB/build")

set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
set(BUILD_SHARED_LIBS OFF)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libgcc -static-libstdc++")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")

option(USE_PRESOLVE "USE PRESOLVE" ON)
option(USE_SCIP "USE SCIP" ON)

#if(USE_PRESOLVE)
#include_directories(
#    papilo/src
#    papilo/src/papilo/external
#)
#endif()
#if(USE_SCIP)
#    scipoptsuite-8.1.0/scip/src
#    scipoptsuite-8.1.0/build/scip
#endif()
find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_library(GMP_LIBRARY NAMES gmp)
if(GMP_INCLUDE_DIR AND GMP_LIBRARY)
    message(STATUS "GMP found")
else()
    message(FATAL_ERROR "GMP not found")
endif()
# 查找 Boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_NO_BOOST_CMAKE ON)
find_package(Boost REQUIRED COMPONENTS serialization program_options iostreams)
if (NOT Boost_FOUND)
  message(FATAL_ERROR "Fatal error: Boost (version >= 1.55) required.")
else()
  message(STATUS "Setting up BOOST")
  message(STATUS " Includes - ${Boost_INCLUDE_DIRS}")
  message(STATUS " Library  - ${Boost_LIBRARIES}")
  include_directories(${Boost_INCLUDE_DIRS})
  link_directories(${Boost_LIBRARY_DIRS})
endif()

# 定义源文件

# 添加可执行文件
#link_directories(${CMAKE_CURRENT_SOURCE_DIR}/../papilo/build)
#link_directories(${CMAKE_CURRENT_SOURCE_DIR}/../oneTBB/build/gnu_11.4_cxx11_64_relwithdebinfo)

#if(USE_PRESOLVE)
#add_subdirectory(papilo)
#set(PAPILO_DIR ${CMAKE_BINARY_DIR})
#find_package(PAPILO)
#endif()

file(GLOB SOURCES "*.cpp")
add_library(DNOP ${SOURCES})

# 针对 DNOP 目标设置包含路径和链接库
#target_include_directories(DNOP PRIVATE
#  ${TBB_INCLUDE_DIRS}
#  ${Boost_INCLUDE_DIRS}
#  ../papilo/src
#  ../papilo/build
#)

#message("${PAPILO_DIR}")
#find_package(PAPILO REQUIRED)
#if (NOT PAPILO_FOUND)
#  message(FATAL_ERROR "FUCK")
#endif()
#file(GLOB_RECURSE headers LIST_DIRECTORIES true ../papilo/src)
#foreach(header ${headers})
#    if(IS_DIRECTORY ${header})
#        target_include_directories(DNOP PRIVATE ${header})
#    endif()
#endforeach()

target_include_directories(DNOP PRIVATE ${GMP_INCLUDE_DIR})

if(USE_PRESOLVE)
target_include_directories(DNOP PRIVATE 
#  ../papilo/build
#  ../papilo/src
  scipoptsuite-8.1.0/build/papilo
  scipoptsuite-8.1.0/papilo/src
  scipoptsuite-8.1.0/papilo/src/papilo/external
)
endif()
if(USE_SCIP)
target_include_directories(DNOP PRIVATE
    scipoptsuite-8.1.0/scip/src
    scipoptsuite-8.1.0/build/scip
)
endif()

if(USE_PRESOLVE)
target_link_directories(DNOP PRIVATE
    scipoptsuite-8.1.0/build/papilo
)
endif()

if(USE_SCIP)
target_link_directories(DNOP PRIVATE
  scipoptsuite-8.1.0/build/lib
)
endif()

target_link_libraries(DNOP PRIVATE
  ${GMP_LIBRARY}
)

if(USE_PRESOLVE)
target_link_libraries(DNOP PRIVATE
#  ${PAPILO_IMPORTED_TARGETS}
  papilo-core
  ${Boost_LIBRARIES} Boost::serialization Boost::program_options Boost::iostreams
  #-lboost_serialization -lboost_program_options -lboost_iostreams
)
endif()
if(USE_SCIP)
target_link_libraries(DNOP PRIVATE
  scip 
  soplex-pic
)
endif()

if(USE_PRESOLVE)
  target_compile_definitions(DNOP PRIVATE -DUSEPRESOLVE)
endif()

if(USE_SCIP)
  target_compile_definitions(DNOP PRIVATE -DUSE_SCIP)
endif()

# 如果有额外的依赖或配置文件，包括它们
#list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/../papilo/cmake")
#include(Dependencies)
