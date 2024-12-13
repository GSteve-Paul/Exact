set display verblevel 0
set timing enabled FALSE
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/SOS/sparse2.lp"
optimize
write statistics temp/sparse2.lp_r1.stats
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/SOS/sparse2.lp"
optimize
write statistics temp/sparse2.lp_r2.stats
quit
