set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/p0033.osil"
write problem temp/p0033.osil.fzn
presolve
write transproblem temp/p0033.osil_trans.fzn
set heur emph def
read temp/p0033.osil_trans.fzn
optimize
validatesolve "3089" "3089"
read temp/p0033.osil.fzn
optimize
validatesolve "3089" "3089"
quit
