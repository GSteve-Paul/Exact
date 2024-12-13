# Install script for directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src

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
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/soplex" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/array.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/basevectors.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/changesoplex.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/classarray.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/classset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/clufactor.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/clufactor.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/clufactor_rational.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/clufactor_rational.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/cring.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/dataarray.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/datahashtable.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/datakey.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/dataset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/didxset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/dsvector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/dsvectorbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/dvector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/enter.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/exceptions.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/gzstream.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/idlist.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/idxset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/islist.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/leave.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lpcol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lpcolbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lpcolset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lpcolsetbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lprow.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lprowbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lprowset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/lprowsetbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/mpsinput.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/nameset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/notimer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/random.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/rational.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/ratrecon.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/ratrecon.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slinsolver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slinsolver_rational.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slufactor.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slufactor.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slufactor_rational.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/slufactor_rational.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/sol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/solbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/solvedbds.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/solverational.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/solvereal.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/sorter.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxalloc.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxautopr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxautopr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxbasis.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxbasis.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxboundflippingrt.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxboundflippingrt.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxbounds.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxchangebasis.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdantzigpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdantzigpr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdefaultrt.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdefaultrt.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdefines.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdefines.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdesc.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdevexpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxdevexpr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxequilisc.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxequilisc.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxfastrt.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxfastrt.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxfileio.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxfileio.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxgeometsc.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxgeometsc.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxgithash.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxharrisrt.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxharrisrt.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxhybridpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxhybridpr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxid.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxleastsqsc.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxleastsqsc.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxlp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxlpbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxlpbase_rational.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxlpbase_real.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxmainsm.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxmainsm.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxout.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxpapilo.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxparmultpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxparmultpr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxpricer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxquality.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxratiotester.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxscaler.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxscaler.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxshift.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsimplifier.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsolve.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsolver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsolver.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxstarter.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxstarter.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsteepexpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsteeppr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsteeppr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsumst.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxsumst.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxvecs.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxvectorst.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxvectorst.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxweightpr.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxweightpr.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxweightst.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxweightst.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/spxwritestate.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/ssvector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/ssvectorbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/stablesum.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/statistics.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/statistics.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/svector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/svectorbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/svset.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/svsetbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/testsoplex.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/timer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/timerfactory.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/unitvector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/unitvectorbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/updatevector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/updatevector.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/usertimer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/validation.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/validation.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/vector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/vectorbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex/wallclocktimer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex/soplex/config.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/soplex/src/soplex_interface.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex")
    file(RPATH_CHECK
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex"
         RPATH "/usr/local/lib")
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE EXECUTABLE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/soplex")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex")
    file(RPATH_CHANGE
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex"
         OLD_RPATH "::::::::::::::"
         NEW_RPATH "/usr/local/lib")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/soplex")
    endif()
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libsoplex.a")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libsoplex-pic.a")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  foreach(file
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so.6.0.4.0"
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so.6.0"
      )
    if(EXISTS "${file}" AND
       NOT IS_SYMLINK "${file}")
      file(RPATH_CHECK
           FILE "${file}"
           RPATH "")
    endif()
  endforeach()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE SHARED_LIBRARY FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libsoplexshared.so.6.0.4.0"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libsoplexshared.so.6.0"
    )
  foreach(file
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so.6.0.4.0"
      "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so.6.0"
      )
    if(EXISTS "${file}" AND
       NOT IS_SYMLINK "${file}")
      if(CMAKE_INSTALL_DO_STRIP)
        execute_process(COMMAND "/usr/bin/strip" "${file}")
      endif()
    endif()
  endforeach()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so")
    file(RPATH_CHECK
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so"
         RPATH "")
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE SHARED_LIBRARY FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libsoplexshared.so")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libsoplexshared.so")
    endif()
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex/soplex-targets.cmake")
    file(DIFFERENT EXPORT_FILE_CHANGED FILES
         "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex/soplex-targets.cmake"
         "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex/src/CMakeFiles/Export/lib/cmake/soplex/soplex-targets.cmake")
    if(EXPORT_FILE_CHANGED)
      file(GLOB OLD_CONFIG_FILES "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex/soplex-targets-*.cmake")
      if(OLD_CONFIG_FILES)
        message(STATUS "Old export file \"$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex/soplex-targets.cmake\" will be replaced.  Removing files [${OLD_CONFIG_FILES}].")
        file(REMOVE ${OLD_CONFIG_FILES})
      endif()
    endif()
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex/src/CMakeFiles/Export/lib/cmake/soplex/soplex-targets.cmake")
  if("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex/src/CMakeFiles/Export/lib/cmake/soplex/soplex-targets-release.cmake")
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/soplex" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex/CMakeFiles/soplex-config.cmake"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/soplex-config-version.cmake"
    )
endif()

