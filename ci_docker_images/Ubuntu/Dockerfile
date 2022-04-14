# Filename: Dockerfile 
FROM gcc
RUN apt update && apt -y install make autoconf cmake libboost-dev apt-utils clang clang-format coinor-libcoinutils-dev git python3 pip

WORKDIR /usr/src/app

RUN git clone https://gitlab.com/MIAOresearch/VeriPB.git
RUN pip3 install ./VeriPB
