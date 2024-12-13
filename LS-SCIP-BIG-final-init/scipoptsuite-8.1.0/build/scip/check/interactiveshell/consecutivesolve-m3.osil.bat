set display verblevel 0
set timing enabled FALSE
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MINLP/m3.osil"
optimize
write statistics temp/m3.osil_r1.stats
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MINLP/m3.osil"
optimize
write statistics temp/m3.osil_r2.stats
quit
