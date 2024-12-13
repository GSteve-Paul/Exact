set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/lseu.mps"
write problem temp/lseu.mps.lp
presolve
write transproblem temp/lseu.mps_trans.lp
set heur emph def
read temp/lseu.mps_trans.lp
optimize
validatesolve "1120" "1120"
read temp/lseu.mps.lp
optimize
validatesolve "1120" "1120"
quit
