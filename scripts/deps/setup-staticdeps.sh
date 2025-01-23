#!/usr/bin/env bash

./scripts/deps/setup-gtest.sh
./scripts/deps/setup-outputcheck.sh

set -e -u -o pipefail

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}"/install)
lib_dir=$(readlink -fm "${dep_dir}"/install/lib/)
echo "export LD_LIBRARY_PATH=$lib_dir:\$LD_LIBRARY_PATH" >> ~/.bashrc

[ ! -d "${install_dir}" ] && mkdir -p "${install_dir}"

dep="minisat"

cd "${dep_dir}"
git clone https://github.com/stp/minisat "${dep}" || true
cd "${dep}"
mkdir build && cd build
cmake -DBUILD_SHARED_LIBS=OFF -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..

dep="cms"


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
mkdir build && cd build
cmake -DSTATS=OFF -DSTATICCOMPILE=ON -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
cmake --build . --parallel "$(nproc)"
cmake --install .
cd ..




cd "${dep_dir}"

git clone https://github.com/meelgroup/louvain-community || true
cd louvain-community
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" -DSTATICCOMPILE=ON ..
make -j10
cd ../..

git clone https://github.com/meelgroup/sbva || true
cd sbva
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}"  -DSTATICCOMPILE=ON ..
make -j8
cd ../..

git clone https://github.com/meelgroup/arjun || true
cd arjun
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}"  -DSTATICCOMPILE=ON ..
make -j8
cd ../..

git clone https://github.com/meelgroup/approxmc || true
cd approxmc
mkdir build && cd build
cmake  -DSTATICCOMPILE=ON -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/meelgroup/unigen/ || true
cd unigen
mkdir build && cd build
cmake  -DSTATICCOMPILE=ON -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..

git clone https://github.com/arijitsh/cmsgen/ || true
cd cmsgen
mkdir build && cd build
cmake  -DSTATICCOMPILE=ON -DCMAKE_INSTALL_PREFIX:PATH="${install_dir}" ..
make -j8
cd ../..