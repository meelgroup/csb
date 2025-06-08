#!/bin/bash
set -e
set -x

rm -rf tests tools lib bindings include
rm -rf CM* Makefile ./*.cmake build.ninja .cmake
rm -rf stp*
rm -rf cmake*
cmake -DENABLE_TESTING=ON -DSTATICCOMPILE=ON -DFORCE_CMS=ON -DUSE_UNIGEN=OFF -DNOUNIGEN=ON ..
make -j20 VERBOSE=1
