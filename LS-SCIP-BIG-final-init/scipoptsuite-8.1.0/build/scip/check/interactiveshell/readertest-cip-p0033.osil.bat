set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/p0033.osil"
write problem temp/p0033.osil.cip
presolve
write transproblem temp/p0033.osil_trans.cip
set heur emph def
read temp/p0033.osil_trans.cip
optimize
validatesolve "3089" "3089"
read temp/p0033.osil.cip
optimize
validatesolve "3089" "3089"
quit
