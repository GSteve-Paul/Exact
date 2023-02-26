#!/usr/bin/env bash

mkdir -p exact/headers
cd ../src
for f in *.h*; do cp --parents $f ../python/exact/headers; done
for f in */*.h*; do cp --parents $f ../python/exact/headers; done
for f in */*/*.h*; do cp --parents $f ../python/exact/headers; done
cd ../python
cp ../README.md exact/README.md
cp ../LICENSE exact/used_licenses/LICENSE
mkdir -p exact/used_licenses
cp ../src/used_licenses/COPYING exact/used_licenses/COPYING
