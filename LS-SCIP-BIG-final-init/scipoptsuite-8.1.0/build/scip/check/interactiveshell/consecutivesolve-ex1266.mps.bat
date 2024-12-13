set display verblevel 0
set timing enabled FALSE
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MINLP/ex1266.mps"
optimize
write statistics temp/ex1266.mps_r1.stats
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MINLP/ex1266.mps"
optimize
write statistics temp/ex1266.mps_r2.stats
quit
