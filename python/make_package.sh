#!/usr/bin/env bash

oldversion="= \"$1\""
newversion="= \"$2\""

sed -i "s/$oldversion/$newversion/" setup.py
sed -i "s/$oldversion/$newversion/" pyproject.toml
sed -i "s/$oldversion/$newversion/" exact/__init__.py

mkdir -p exact/headers/constraints
mkdir -p exact/headers/datastructures
mkdir -p exact/headers/propagation
mkdir -p exact/headers/used_licenses
cp ../src/constraints/*.hpp exact/headers/constraints
cp ../src/datastructures/*.hpp exact/headers/datastructures
cp ../src/propagation/*.hpp exact/headers/propagation
cp ../src/used_licenses/*.hpp exact/headers/used_licenses
cp ../src/*.hpp exact/headers
cp ../README.md README.md

cp ../build_lib/libExact.so exact/libExact.so

poetry build
# poetry publish
