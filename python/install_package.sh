#!/usr/bin/env bash

threads=$1
if [ $# -eq 0 ]
  then threads=8
fi

echo $threads

./copy_headers.sh

# compile shared library
cmake .. -DCMAKE_BUILD_TYPE=Release -Dbuild_result=SharedLib -Dbuild_static=OFF -Dsoplex=OFF
# cmake .. -DCMAKE_BUILD_TYPE=Debug -Dbuild_result=SharedLib -Dbuild_static=OFF -Dsoplex=OFF
make -j $threads
cp libExact.so exact/libExact.so
# NOTE: the python/exact folder contains all files necessary for the python package
# FOR macOS:
# cp libExact.dylib exact/libExact.dylib

# create and install python module
python3 -m pip install . -v
# FOR macOS: when encountering the message that cppyy-backend could not be installed, first install cppyy-cling.

# test on a knapsack example
python3 examples/knapsack_classic.py
