FROM ubuntu:18.04

RUN apt update && apt -y install make autoconf cmake libboost-dev apt-utils clang clang-format coinor-libcoinutils-dev git python3-pip vim python3-venv

# avoid infinite wheel installation time:
RUN pip3 install --upgrade pip setuptools wheel
RUN pip3 install build twine networkx

WORKDIR /usr/src/app

# cmake .. -DCMAKE_BUILD_TYPE=Release -Dbuild_result=SharedLib -Dbuild_static=ON
