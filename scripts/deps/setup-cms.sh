#!/usr/bin/env bash

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="cms"

cd "${dep_dir}"

git clone https://github.com/meelgroup/cadical || true
cd cadical
git checkout mate-only-libraries-1.8.0
./configure
make -j "$(nproc)"
cp build/libcadical.* ${install_dir}/lib/
cd ..

git clone https://github.com/meelgroup/cadiback || true
cd cadiback
git checkout mate
./configure
make -j "$(nproc)"
cp libcadiback.* ${install_dir}/lib/
cd ..

git clone https://github.com/msoos/cryptominisat "${dep}" || true
cd "${dep}"
mkdir build || true
cd build
cmake -DSTATS=OFF -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

# EOF
