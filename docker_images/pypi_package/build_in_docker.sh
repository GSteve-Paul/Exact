#!/usr/bin/env bash

git clone https://gitlab.com/JoD/exact-dev.git
mkdir exact-dev/build_lib
cd exact-dev/build_lib
git checkout release
cmake .. -DCMAKE_BUILD_TYPE=Release -Dbuild_result=SharedLib -Dbuild_static=ON
make -j 8
cd ../python
./make_package.sh 0.5.3 1.0.0
