### Full Build from Source on Linux
If you want to build `csb` from source manually, you will need to follow these steps:

```
sudo apt install git cmake bison flex libboost-all-dev python3 perl build-essential python3-distutils-extra wget
sudo apt install zlib1g-dev libboost-program-options-dev libboost-serialization-dev libgmp-dev libmpfr-dev
git clone https://github.com/meelgroup/csb
cd csb
./scripts/deps/setup-csb.sh
mkdir build && cd build
cmake ..
cmake --build .
sudo cmake --install .
```

### Build from Source on MacOS

1. Install the toolchain and solver prerequisites from Homebrew
```
brew update
brew install bison cmake boost gmp mpfr wget zig
```
2. Export the same compiler and linker flags used in CI so Homebrew’s MPFR/GMP headers and libs are found

```
export MPFR_PREFIX="$(brew --prefix mpfr)"
export GMP_PREFIX="$(brew --prefix gmp)"
export BISON_PREFIX="$(brew --prefix bison)"
export CPPFLAGS="-I${MPFR_PREFIX}/include -I${GMP_PREFIX}/include ${CPPFLAGS:-}"
export CXXFLAGS="-I${MPFR_PREFIX}/include -I${GMP_PREFIX}/include ${CXXFLAGS:-}"
export CFLAGS="-I${MPFR_PREFIX}/include -I${GMP_PREFIX}/include ${CFLAGS:-}"
export LDFLAGS="-L${MPFR_PREFIX}/lib -L${GMP_PREFIX}/lib -lmpfr -lgmp ${LDFLAGS:-}"
export PATH="${BISON_PREFIX}/bin:${PATH}"
```
3. Fetch CSB and build its third-party dependencies
```
git clone https://github.com/meelgroup/csb
cd csb
STATICCOMPILE=OFF ./scripts/deps/setup-csb.sh
# Configure, build, and install CSB itself
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=OFF ..
cmake --build . --config Release
sudo cmake --install .
```