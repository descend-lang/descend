#!/bin/sh

g++ -Wall -Wextra -D CL_TARGET_OPENCL_VERSION=300 tree_reduce.cpp -o tree_reduce.out -lOpenCL
if [[ $1 == "-e" ]]
then
    ./tree_reduce.out
fi