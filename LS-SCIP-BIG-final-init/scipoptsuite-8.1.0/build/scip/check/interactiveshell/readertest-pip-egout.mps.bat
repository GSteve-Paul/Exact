set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/egout.mps"
write problem temp/egout.mps.pip
presolve
write transproblem temp/egout.mps_trans.pip
set heur emph def
read temp/egout.mps_trans.pip
optimize
validatesolve "568.1007" "568.1007"
read temp/egout.mps.pip
optimize
validatesolve "568.1007" "568.1007"
quit
