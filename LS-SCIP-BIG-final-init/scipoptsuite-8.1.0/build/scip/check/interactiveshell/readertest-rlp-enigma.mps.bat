set heur emph off
read "/mnt/e/product/c/LS-SCIP/scipoptsuite-8.1.0/scip"/check/"instances/MIP/enigma.mps"
write problem temp/enigma.mps.rlp
presolve
write transproblem temp/enigma.mps_trans.rlp
set heur emph def
read temp/enigma.mps_trans.rlp
optimize
validatesolve "0" "0"
read temp/enigma.mps.rlp
optimize
validatesolve "0" "0"
quit
