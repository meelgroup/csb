#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)
lib_dir=$(readlink -fm "${dep_dir}"/install/lib/)
echo "export LD_LIBRARY_PATH=$lib_dir:\$LD_LIBRARY_PATH" >> ~/.bashrc

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

cd "${dep_dir}"

git clone https://github.com/meelgroup/louvain-community
cd louvain-community
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j10
cd ../..

git clone https://github.com/meelgroup/sbva
cd sbva
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/meelgroup/arjun
cd arjun
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/meelgroup/approxmc
cd approxmc
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/meelgroup/unigen/
cd unigen
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/arijitsh/cmsgen/
cd cmsgen
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

# EOF
