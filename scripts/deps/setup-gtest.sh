#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="gtest"

cd "${dep_dir}"
git clone https://github.com/stp/googletest "${dep}"
cd "${dep}"
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . 
cmake --install .
cd ..

# EOF
