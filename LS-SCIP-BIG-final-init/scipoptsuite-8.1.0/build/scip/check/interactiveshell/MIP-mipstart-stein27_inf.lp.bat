read /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/check/instances/MIP/stein27_inf.lp
read /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/check/mipstarts/stein27_inf.lp.mst
presolve
validatesolve +infinity +infinity
read /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/check/instances/MIP/stein27_inf.lp
read /mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip/check/mipstarts/stein27_inf.lp.mst
set heuristics completesol beforepresol FALSE
optimize
validatesolve +infinity +infinity
quit
