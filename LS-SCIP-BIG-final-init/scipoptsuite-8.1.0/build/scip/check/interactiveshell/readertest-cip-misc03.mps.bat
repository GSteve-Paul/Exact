set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/misc03.mps"
write problem temp/misc03.mps.cip
presolve
write transproblem temp/misc03.mps_trans.cip
set heur emph def
read temp/misc03.mps_trans.cip
optimize
validatesolve "3360" "3360"
read temp/misc03.mps.cip
optimize
validatesolve "3360" "3360"
quit
