set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/stein27_inf.lp"
write problem temp/stein27_inf.lp.opb
presolve
write transproblem temp/stein27_inf.lp_trans.opb
set heur emph def
read temp/stein27_inf.lp_trans.opb
optimize
validatesolve "+infinity" "+infinity"
read temp/stein27_inf.lp.opb
optimize
validatesolve "+infinity" "+infinity"
quit
