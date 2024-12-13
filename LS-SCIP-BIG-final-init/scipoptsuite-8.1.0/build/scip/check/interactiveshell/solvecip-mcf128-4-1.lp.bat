read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/Indicator/mcf128-4-1.lp"
write problem temp/mcf128-4-1.lp.cip
read temp/mcf128-4-1.lp.cip
optimize
validatesolve "14" "14"
quit
