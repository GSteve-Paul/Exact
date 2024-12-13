set display verblevel 0
set timing enabled FALSE
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/blend2.mps"
optimize
write statistics temp/blend2.mps_r1.stats
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/blend2.mps"
optimize
write statistics temp/blend2.mps_r2.stats
quit
