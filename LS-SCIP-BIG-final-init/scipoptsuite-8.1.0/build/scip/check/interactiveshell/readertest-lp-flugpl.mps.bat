set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/flugpl.mps"
write problem temp/flugpl.mps.lp
presolve
write transproblem temp/flugpl.mps_trans.lp
set heur emph def
read temp/flugpl.mps_trans.lp
optimize
validatesolve "1201500" "1201500"
read temp/flugpl.mps.lp
optimize
validatesolve "1201500" "1201500"
quit
