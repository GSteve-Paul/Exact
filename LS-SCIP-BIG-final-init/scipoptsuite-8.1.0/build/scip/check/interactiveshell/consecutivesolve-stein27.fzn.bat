set display verblevel 0
set timing enabled FALSE
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/stein27.fzn"
optimize
write statistics temp/stein27.fzn_r1.stats
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/stein27.fzn"
optimize
write statistics temp/stein27.fzn_r2.stats
quit
