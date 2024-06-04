FROM quay.io/pypa/manylinux_2_28_x86_64

RUN dnf install wget -y
RUN wget -O boost_1_81_0.tar.gz https://sourceforge.net/projects/boost/files/boost/1.81.0/boost_1_81_0.tar.gz/download
RUN mkdir boost-ver
RUN cd boost-ver && tar -xzf ../boost_*.tar.gz
WORKDIR boost-ver/boost_1_81_0
RUN ./bootstrap.sh
RUN ./b2 install --prefix=/usr/local
RUN /opt/python/cp310-cp310/bin/python -m pip install twine
RUN /opt/python/cp311-cp311/bin/python -m pip install twine
RUN /opt/python/cp312-cp312/bin/python -m pip install twine
WORKDIR /
