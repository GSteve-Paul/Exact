#!/bin/bash

for run in {1..100}; do
  killall Exact --signal 9; killall veripb --signal 9
  echo $run
  sleep 0.1
done


