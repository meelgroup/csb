#!/usr/bin/env bash

set -x
set -euo pipefail

# Build configuration
BUILD_TYPE="${BUILD_TYPE:-Release}"
STATICCOMPILE="${STATICCOMPILE:-ON}"

dep_dir="deps"
install_dir=$(readlink -fm "${dep_dir}/install")
lib_dir=$(readlink -fm "${install_dir}/lib")
bin_dir=$(readlink -fm "${install_dir}/bin")
export LD_LIBRARY_PATH="$lib_dir:${LD_LIBRARY_PATH-}"
export PATH="$bin_dir:${PATH-}"
export CMAKE_PREFIX_PATH="$install_dir:${CMAKE_PREFIX_PATH-}"
echo "export LD_LIBRARY_PATH=$lib_dir:\$LD_LIBRARY_PATH" >> ~/.bashrc
echo "export PATH=$bin_dir:\$PATH" >> ~/.bashrc
echo "export CMAKE_PREFIX_PATH=$install_dir:\$CMAKE_PREFIX_PATH" >> ~/.bashrc

mkdir -p "$install_dir" "$dep_dir"
cd "$dep_dir"

os=$(uname)
if [[ "$os" == "Darwin" ]]; then
  if [[ "$STATICCOMPILE" == "ON" ]]; then
    wget https://www.zlib.net/zlib-1.3.1.tar.gz
    tar xzvf zlib-1.3.1.tar.gz
    (cd zlib-1.3.1 && ./configure --static && make -j8 && sudo make install)
  else
    wget https://www.zlib.net/zlib-1.3.1.tar.gz
    tar xzvf zlib-1.3.1.tar.gz
    (cd zlib-1.3.1 && ./configure && make -j8 && sudo make install)
  fi

  wget https://ftp.gnu.org/gnu/mpfr/mpfr-4.2.1.tar.xz
  tar xf mpfr-4.2.1.tar.xz
  (cd mpfr-4.2.1 && ./configure --enable-static -enable-cxx --enable-shared && make -j8 && sudo make install)
fi

git clone https://github.com/stp/minisat minisat
(cd minisat && mkdir build && cd build && cmake -DBUILD_SHARED_LIBS=OFF -DSTATICCOMPILE=ON -DCMAKE_INSTALL_PREFIX:PATH="$install_dir" .. && cmake --build . --parallel "$(nproc)" && cmake --install .)
exit 0
# Solver dependencies
git clone --branch add_dynamic_lib https://github.com/meelgroup/cadical cadical
(cd cadical && CXXFLAGS=-fPIC ./configure --competition && make -j"$(nproc)")

git clone --branch synthesis https://github.com/meelgroup/cadiback cadiback
cd cadiback && CXX=c++ ./configure && make -j"$(nproc)" && cd ..

git clone --recurse-submodules https://github.com/msoos/cryptominisat cryptominisat
(cd cryptominisat && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" .. && make -j20)

git clone https://github.com/meelgroup/SBVA sbva
(cd sbva && mkdir build && cd build && ln -s ../scripts/*.sh . && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" -DCMAKE_INSTALL_PREFIX="$install_dir" .. && cmake --build . --config "$BUILD_TYPE" -v && make -j20)

git clone https://github.com/meelgroup/breakid breakid
(cd breakid && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" -DCMAKE_INSTALL_PREFIX="$install_dir" .. && cmake --build . --config "$BUILD_TYPE" -v && make -j20)

wget https://ensmallen.org/files/ensmallen-2.21.1.tar.gz
tar xvf ensmallen-2.21.1.tar.gz
(cd ensmallen-2.21.1 && mkdir -p build && cd build && cmake -DCMAKE_POLICY_VERSION_MINIMUM=3.5 .. && cmake --build . --config "$BUILD_TYPE" -v && cmake --install . --config "$BUILD_TYPE" -v)

wget https://github.com/USCiLab/cereal/archive/v1.3.2.tar.gz
tar xvf v1.3.2.tar.gz
(cd cereal-1.3.2 && mkdir -p build && cd build && cmake -DJUST_INSTALL_CEREAL=ON .. && cmake --build . --config "$BUILD_TYPE" -v && cmake --install . --config "$BUILD_TYPE" -v)

wget https://sourceforge.net/projects/arma/files/armadillo-14.0.2.tar.xz
tar xvf armadillo-14.0.2.tar.xz
(cd armadillo-14.0.2 && ./configure && make -j6 &&  make install)


git clone --branch 4.4.0 https://github.com/mlpack/mlpack mlpack
(cd mlpack && mkdir -p build && cd build && cmake -DBUILD_SHARED_LIBS=ON -DBUILD_CLI_EXECUTABLES=OFF .. && cmake --build . --config "$BUILD_TYPE" -v && cmake --install . --config "$BUILD_TYPE" -v)

git clone https://github.com/meelgroup/arjun arjun
(cd arjun && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DSTATICCOMPILE="$STATICCOMPILE" -DENABLE_TESTING=OFF -DCMAKE_INSTALL_PREFIX="$install_dir" -S .. && cmake --build . --config "$BUILD_TYPE" -v && make -j"$(nproc)")

git clone https://github.com/meelgroup/approxmc approxmc
(cd approxmc && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DSTATICCOMPILE="$STATICCOMPILE" -DENABLE_TESTING=OFF -S .. && cmake --build . --config "$BUILD_TYPE" -v && make -j"$(nproc)")
# ln -sfn "$PWD/approxmc" ..


wget https://github.com/flintlib/flint/releases/download/v3.2.0-rc1/flint-3.2.0-rc1.tar.gz
tar xzf flint-3.2.0-rc1.tar.gz
(
  cd flint-3.2.0-rc1
  ./configure --enable-static --enable-shared --prefix="$install_dir"
  make -j"$(nproc)"
  make install
)


git clone https://github.com/meelgroup/ganak ganak
(cd ganak && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" .. && make -j"$(nproc)")
# ln -sfn "$PWD/ganak" ..



git clone https://github.com/arijitsh/cmsgen cmsgen
(cd cmsgen && mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DCMAKE_INSTALL_PREFIX:PATH="$install_dir" -DSTATICCOMPILE="$STATICCOMPILE" .. && cmake --build . --config "$BUILD_TYPE" -v && make -j"$(nproc)")

git clone https://github.com/meelgroup/unigen unigen
cd unigen && mkdir -p build && cd build && cmake -DCMAKE_INSTALL_PREFIX:PATH="$install_dir" -DSTATICCOMPILE="$STATICCOMPILE" .. && make -j"$(nproc)" && cd ../..

# EOF

