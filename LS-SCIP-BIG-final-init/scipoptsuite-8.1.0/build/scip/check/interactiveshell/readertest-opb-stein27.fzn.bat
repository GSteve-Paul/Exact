set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/stein27.fzn"
write problem temp/stein27.fzn.opb
presolve
write transproblem temp/stein27.fzn_trans.opb
set heur emph def
read temp/stein27.fzn_trans.opb
optimize
validatesolve "18" "18"
read temp/stein27.fzn.opb
optimize
validatesolve "18" "18"
quit
