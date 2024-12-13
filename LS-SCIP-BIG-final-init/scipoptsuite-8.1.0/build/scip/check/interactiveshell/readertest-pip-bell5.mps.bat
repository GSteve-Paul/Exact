set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/bell5.mps"
write problem temp/bell5.mps.pip
presolve
write transproblem temp/bell5.mps_trans.pip
set heur emph def
read temp/bell5.mps_trans.pip
optimize
validatesolve "8966406.49" "8966406.49"
read temp/bell5.mps.pip
optimize
validatesolve "8966406.49" "8966406.49"
quit
