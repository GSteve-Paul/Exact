#!/bin/bash

# usage: ../test/run_all.sh 3 "testruns" /home/jod/workspace/exact-dev/build_testruns/Exact

# to kill: killall Exact --signal 9; killall veripb --signal 9 (multiple times until it reports no process busy)

logfolder="/tmp/Exact/$2"
SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"

declare -a arr_configs=(
"simple"
"arbitrary"
"noproof"
"mindiv"
"rto"
"slack+1"
)

for idx in "${!arr_configs[@]}"; do
    config=${arr_configs[$idx]}
    mkdir -p `dirname $logfolder/$config.txt`
    $SCRIPTPATH/run_tests_$config.sh $1 $2 $3 $4 &> $logfolder/$config.txt &
done
