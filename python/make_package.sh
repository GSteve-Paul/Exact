#!/usr/bin/env bash

threads=$1
if [ $# -eq 0 ]
  then threads=8
fi

echo $threads

# get the header files in the right place
mkdir -p exact/headers/constraints
mkdir -p exact/headers/datastructures
mkdir -p exact/headers/propagation
mkdir -p exact/headers/used_licenses
mkdir -p exact/used_licenses
cp ../src/constraints/*.hpp exact/headers/constraints
cp ../src/datastructures/*.hpp exact/headers/datastructures
cp ../src/propagation/*.hpp exact/headers/propagation
cp ../src/used_licenses/*.hpp exact/headers/used_licenses
cp ../src/*.hpp exact/headers
cp ../README.md README.md
cp ../LICENSE LICENSE
cp ../src/used_licenses/COPYING exact/used_licenses/COPYING

# compile shared library
cmake .. -DCMAKE_BUILD_TYPE=Release -Dbuild_result=SharedLib -Dbuild_static=OFF -Dsoplex=OFF
make -j $threads
cp libExact.so exact/libExact.so

# create and install python module
python3 -m pip install . -v

# test on a knapsack example
python3 examples/knapsack_classic.py
