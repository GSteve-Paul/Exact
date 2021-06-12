#!/bin/bash

cmake configure ..
make -j
cp Exact Exact_$(git rev-parse --short HEAD)
