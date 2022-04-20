#!/usr/bin/env bash

# usage: ./make_package.sh 0.4.0 0.5.0

oldversion="= \"$1\""
newversion="= \"$2\""

sed -i "s/$oldversion/$newversion/" setup.py
sed -i "s/$oldversion/$newversion/" pyproject.toml
sed -i "s/$oldversion/$newversion/" exact/__init__.py

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

cd ../build_lib
cmake .. -DCMAKE_BUILD_TYPE=Release -Dbuild_result=SharedLib -Dbuild_static=ON
make -j 8
# ninja -j 8

cd ../python
cp ../build_lib/libExact.so exact/libExact.so
strip --strip-unneeded exact/libExact.so

poetry build
# poetry publish
