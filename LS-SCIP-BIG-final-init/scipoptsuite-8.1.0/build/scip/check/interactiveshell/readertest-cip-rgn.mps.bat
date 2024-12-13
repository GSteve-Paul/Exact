set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/rgn.mps"
write problem temp/rgn.mps.cip
presolve
write transproblem temp/rgn.mps_trans.cip
set heur emph def
read temp/rgn.mps_trans.cip
optimize
validatesolve "82.19999924" "82.19999924"
read temp/rgn.mps.cip
optimize
validatesolve "82.19999924" "82.19999924"
quit
