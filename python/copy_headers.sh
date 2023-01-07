#!/usr/bin/env bash

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
cp ../LICENSE exact/used_licenses/LICENSE
cp ../src/used_licenses/COPYING exact/used_licenses/COPYING
