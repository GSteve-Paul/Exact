# Install script for directory: /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src

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
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/gcg" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_empty.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_bpstrong.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_generic.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_orig.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_relpsprob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/branch_ryanfoster.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_conspartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_indexpartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/miscvisualization.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_pricingcontroller.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_pricingtype.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_partialdecomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_detprobdata.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_stabilization.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/class_varpartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_consnamelevenshtein.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_consnamenonumbers.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_gamsdomain.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_gamssymbol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_miplibconstypes.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_nnonzeros.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clscons_scipconstypes.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clsvar_gamsdomain.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clsvar_gamssymbol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clsvar_objvalues.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clsvar_objvaluesigns.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/clsvar_scipvartypes.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/colpool.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/cons_decomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/cons_decomp.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/cons_integralorig.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/cons_masterbranch.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/cons_origbranch.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_compgreedily.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_connected_noNewLinkingVars.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_connectedbase.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_consclass.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_constype.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_dbscan.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_densemasterconss.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_generalmastersetcover.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_generalmastersetpack.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_generalmastersetpart.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_hcgpartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_hrcgpartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_hrgpartition.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_mastersetcover.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_mastersetpack.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_mastersetpart.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_mst.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_neighborhoodmaster.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_postprocess.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_staircase_lsp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_stairheur.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_varclass.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/decomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dialog_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dialog_graph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dialog_master.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/disp_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/disp_master.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/event_bestsol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/event_display.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/event_mastersol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/event_relaxsol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/event_solvingstats.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcgcol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcg_general.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcggithash.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcgplugins.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcgpqueue.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/gcgsort.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgcoefdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgdins.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgfeaspump.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgfracdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgguideddiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcglinesdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgpscostdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgrens.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgrins.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgrounding.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgshifting.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgsimplerounding.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgveclendiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_gcgzirounding.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_greedycolsel.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_mastercoefdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_masterdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_masterfracdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_masterlinesdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_mastervecldiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_origdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_relaxcolsel.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_restmaster.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_setcover.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_xpcrossover.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/heur_xprins.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/masterplugins.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/nodesel_master.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/objdialog.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/objpricer_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/params_visu.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/presol_roundbound.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pricer_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pricestore_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pricingjob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pricingprob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_bliss.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_colpool.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_decomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_gcgcol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_gcgheur.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_gcgsepa.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_gcgpqueue.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_gcgvar.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_pricingjob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_pricingprob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/pub_solver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_blk.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_cls.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_dec.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_gp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_ref.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/reader_tex.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/relax_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/scip_misc.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/scoretype.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/sepa_basis.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/sepa_master.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/solver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/solver_cliquer.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/solver_knapsack.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/solver_mip.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/solver_xyz.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/stat.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_branchgcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_colpool.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_decomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_detector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_gcgcol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_gcgpqueue.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_pricestore_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_pricingjob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_pricingprob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_solver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/struct_vardata.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_branchgcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_classifier.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_colpool.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_consclassifier.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_decomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_detector.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_gcgcol.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_gcgpqueue.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_masterdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_origdiving.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_parameter.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_pricestore_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_pricingjob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_pricingprob.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_pricingstatus.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_scoretype.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_solver.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/type_varclassifier.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/wrapper_partialdecomp.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/bliss_automorph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/bliss_automorph.hpp"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/dec_isomorph.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/gcg/graph" TYPE FILE FILES
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/bipartitegraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/bipartitegraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/bridge.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/columngraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/columngraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graph_gcg.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graph_interface.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graph_tclique.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graphalgorithms.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/graphalgorithms_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hypercolgraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hypercolgraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hypergraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hypergraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hyperrowcolgraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hyperrowcolgraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hyperrowgraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/hyperrowgraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/matrixgraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/matrixgraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/rowgraph.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/rowgraph_def.h"
    "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/gcg/src/graph/weights.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg")
    file(RPATH_CHECK
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg"
         RPATH "/usr/local/lib")
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE EXECUTABLE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/bin/gcg")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg")
    file(RPATH_CHANGE
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg"
         OLD_RPATH "::::::::::::::"
         NEW_RPATH "/usr/local/lib")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/gcg")
    endif()
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/lib/libgcg.a")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg/gcg-targets.cmake")
    file(DIFFERENT EXPORT_FILE_CHANGED FILES
         "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg/gcg-targets.cmake"
         "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/gcg/src/CMakeFiles/Export/lib/cmake/gcg/gcg-targets.cmake")
    if(EXPORT_FILE_CHANGED)
      file(GLOB OLD_CONFIG_FILES "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg/gcg-targets-*.cmake")
      if(OLD_CONFIG_FILES)
        message(STATUS "Old export file \"$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg/gcg-targets.cmake\" will be replaced.  Removing files [${OLD_CONFIG_FILES}].")
        file(REMOVE ${OLD_CONFIG_FILES})
      endif()
    endif()
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/gcg/src/CMakeFiles/Export/lib/cmake/gcg/gcg-targets.cmake")
  if("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/gcg/src/CMakeFiles/Export/lib/cmake/gcg/gcg-targets-release.cmake")
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gcg" TYPE FILE FILES "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/build/gcg/CMakeFiles/gcg-config.cmake")
endif()

