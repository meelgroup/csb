#!/usr/bin/env bash

set -x
set -euo pipefail

# Build configuration
BUILD_TYPE="${BUILD_TYPE:-Release}"
STATICCOMPILE="${STATICCOMPILE:-ON}"

# Git dependency revisions
# Minisat csb branch commit capturing the static macOS toolchain updates.
MINISAT_REF="8c9ea22aff06fdf284b8bb13f8524a96f7d446af"
CADICAL_REF="81de5d2b5c68727b4d183ec5ceb56561f1b3b6e1"
CADIBACK_REF="a35c4b98b6237b16ca0fd08dded8f8f51ff998a8"
CRYPTOMINISAT_REF="b09bd6bf05253adf5981e44f9dbd374b2811ff94"
SBVA_REF="0faa08cf3cc26ed855831c9dc16a3489c9ae010f"
BREAKID_REF="dee9744b7041cec373aa0489128b06a40fce43a1"
MLPACK_REF="34dff29aeeb424beed60579866a2a5d9ed31fab9"
ARJUN_REF="58ec9aff687c9adcd6a26f158a947c07794e43f6"
APPROXMC_REF="56042dc9002dee312bb4be283d2bdf8bc2a67827"
GANAK_REF="c060a9083e7f5477fa86b226030fc8cb32259ab1"
CMSGEN_REF="bad5007705c99122f7417ee585aa58bd00cfe491"
UNIGEN_REF="c6823b3aa5cc37335f018eabcc9cc27790519d41"

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

if command -v nproc >/dev/null 2>&1; then
  NPROC=$(nproc)
elif [[ "$os" == "Darwin" ]]; then
  NPROC=$(sysctl -n hw.logicalcpu)
else
  NPROC=1
fi

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

  if ! command -v zig >/dev/null 2>&1; then
    if command -v brew >/dev/null 2>&1; then
      brew install zig
    else
      echo "zig 0.12 or newer is required for macOS static builds" >&2
      exit 1
    fi
  fi
fi

git clone https://github.com/meelgroup/minisat.git minisat
(
  cd minisat
  git checkout "$MINISAT_REF"
  cmake_args=(
    -S .
    -B build
    -DCMAKE_BUILD_TYPE="$BUILD_TYPE"
    -DBUILD_SHARED_LIBS=OFF
    -DSTATICCOMPILE=ON
    -DCMAKE_INSTALL_PREFIX:PATH="$install_dir"
  )
  if [[ "$os" == "Darwin" ]]; then
    cmake_args+=(-DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/zig-macos-static.cmake)
  fi
  cmake "${cmake_args[@]}"
  cmake --build build --parallel "$NPROC"
  cmake --install build --config "$BUILD_TYPE"
)

# Solver dependencies
git clone --branch add_dynamic_lib https://github.com/meelgroup/cadical cadical
(
  cd cadical
  git checkout "$CADICAL_REF"
  CXXFLAGS=-fPIC ./configure --competition
  make -j"$NPROC"
)

git clone --branch synthesis https://github.com/meelgroup/cadiback cadiback
(
  cd cadiback
  git checkout "$CADIBACK_REF"
  CXX=c++ ./configure
  make -j"$NPROC"
)

git clone --recurse-submodules https://github.com/msoos/cryptominisat cryptominisat
(
  cd cryptominisat
  git checkout "$CRYPTOMINISAT_REF"
  git submodule update --init --recursive
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" ..
  make -j20
)

git clone https://github.com/meelgroup/SBVA sbva
(
  cd sbva
  git checkout "$SBVA_REF"
  mkdir build
  cd build
  ln -s ../scripts/*.sh .
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" -DCMAKE_INSTALL_PREFIX="$install_dir" ..
  cmake --build . --config "$BUILD_TYPE" -v
  make -j20
)

git clone https://github.com/meelgroup/breakid breakid
(
  cd breakid
  git checkout "$BREAKID_REF"
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" -DCMAKE_INSTALL_PREFIX="$install_dir" ..
  cmake --build . --config "$BUILD_TYPE" -v
  make -j20
)

wget https://ensmallen.org/files/ensmallen-2.21.1.tar.gz
tar xvf ensmallen-2.21.1.tar.gz
(cd ensmallen-2.21.1 && mkdir -p build && cd build && cmake -DCMAKE_POLICY_VERSION_MINIMUM=3.5 .. && cmake --build . --config "$BUILD_TYPE" -v && cmake --install . --config "$BUILD_TYPE" -v)

wget https://github.com/USCiLab/cereal/archive/v1.3.2.tar.gz
tar xvf v1.3.2.tar.gz
(cd cereal-1.3.2 && mkdir -p build && cd build && cmake -DJUST_INSTALL_CEREAL=ON .. && cmake --build . --config "$BUILD_TYPE" -v && cmake --install . --config "$BUILD_TYPE" -v)

wget https://sourceforge.net/projects/arma/files/armadillo-14.0.2.tar.xz
tar xvf armadillo-14.0.2.tar.xz
(cd armadillo-14.0.2 && ./configure && make -j6 &&  make install)


git clone https://github.com/mlpack/mlpack mlpack
(
  cd mlpack
  git checkout "$MLPACK_REF"
  mkdir -p build
  cd build
  cmake -DBUILD_SHARED_LIBS=ON -DBUILD_CLI_EXECUTABLES=OFF ..
  cmake --build . --config "$BUILD_TYPE" -v
  cmake --install . --config "$BUILD_TYPE" -v
)

git clone https://github.com/meelgroup/arjun arjun
(
  cd arjun
  git checkout "$ARJUN_REF"
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DSTATICCOMPILE="$STATICCOMPILE" -DENABLE_TESTING=OFF -DCMAKE_INSTALL_PREFIX="$install_dir" -S ..
  cmake --build . --config "$BUILD_TYPE" -v
  make -j"$NPROC"
)

git clone --recurse-submodules https://github.com/meelgroup/approxmc approxmc
(
  cd approxmc
  git checkout "$APPROXMC_REF"
  git submodule update --init --recursive
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DSTATICCOMPILE="$STATICCOMPILE" -DENABLE_TESTING=OFF -S ..
  cmake --build . --config "$BUILD_TYPE" -v
  make -j"$NPROC"
)
# ln -sfn "$PWD/approxmc" ..


wget https://github.com/flintlib/flint/releases/download/v3.2.0-rc1/flint-3.2.0-rc1.tar.gz
tar xzf flint-3.2.0-rc1.tar.gz
(
  cd flint-3.2.0-rc1
  ./configure --enable-static --enable-shared --prefix="$install_dir"
  make -j"$NPROC"
  make install
)


git clone https://github.com/meelgroup/ganak ganak
(
  cd ganak
  git checkout "$GANAK_REF"
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DENABLE_TESTING=OFF -DSTATICCOMPILE="$STATICCOMPILE" ..
  make -j"$NPROC"
)
# ln -sfn "$PWD/ganak" ..



git clone https://github.com/arijitsh/cmsgen cmsgen
(
  cd cmsgen
  git checkout "$CMSGEN_REF"
  mkdir build
  cd build
  cmake -DCMAKE_BUILD_TYPE="$BUILD_TYPE" -DCMAKE_INSTALL_PREFIX:PATH="$install_dir" -DSTATICCOMPILE="$STATICCOMPILE" ..
  cmake --build . --config "$BUILD_TYPE" -v
  make -j"$NPROC"
)

git clone https://github.com/meelgroup/unigen unigen
(
  cd unigen
  git checkout "$UNIGEN_REF"
  mkdir -p build
  cd build
  cmake -DCMAKE_INSTALL_PREFIX:PATH="$install_dir" -DSTATICCOMPILE="$STATICCOMPILE" ..
  make -j"$NPROC"
)

# EOF

