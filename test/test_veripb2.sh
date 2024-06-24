#!/usr/bin/env bash

timelim=$1
ctr=0

for file in /home/jod/workspace/exact/test/instances/opb/opt/*
do
  if [[ "$file" == "/home/jod/workspace/exact/test/instances/opb/opt/mult.op" ]]; then
    # non-linear constraints
    continue
  fi
  if [[ "$file" == "/home/jod/workspace/exact/test/instances/opb/opt/testnlc.op" ]]; then
    # non-linear constraints
    continue
  fi
  ctr=$(( ctr + 1 ))
  echo "*** $ctr $file ***"
  /home/jod/workspace/exact/build_profile/Exact $file --timeout=$timelim --proof-log=/tmp/out$ctr --proof-assumptions=0 --verbosity=0 --print-uniform=0
  sleep 0.1
  echo ""
  veripb $file /tmp/out$ctr.proof --arbitraryPrecision --no-requireUnsat
  echo ""
done

for file in /home/jod/workspace/exact/test/instances/opb/dec/*
do
  ctr=$(( ctr + 1 ))
  echo "*** $ctr $file ***"
  /home/jod/workspace/exact/build_profile/Exact $file --timeout=$timelim --proof-log=/tmp/out$ctr --proof-assumptions=0 --verbosity=0 --print-uniform=0
  sleep 0.1
  echo ""
  veripb $file /tmp/out$ctr.proof --arbitraryPrecision --no-requireUnsat
  echo ""
done
