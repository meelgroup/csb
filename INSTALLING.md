## Detailed Building and Installation for (and from) STP

STP is built with [CMake](https://cmake.org/), version 3.0.2 or newer. CMake is a
meta build system that generates build files for other tools such as
make(1), Visual Studio, Xcode, etc.

### Configuration variables
Here are a few interesting configuration variables. These apply to all
generators.

- `CMAKE_BUILD_TYPE` - The build type (e.g. Release)
- `CMAKE_INSTALL_PREFIX` - The prefix for install (e.g. /usr/local )
- `ENABLE_ASSERTIONS` - If TRUE STP will be built with asserts.
- `ENABLE_TESTING` - Enable running tests
- `ENABLE_PYTHON_INTERFACE` - Enable building the Python interface
- `PYTHON_EXECUTABLE` - Set python executable in case you have more than one python installed
- `SANITIZE` - Use Clang's sanitization checks
- `STATICCOMPILE` - Build static libraries and binaries instead of dynamic

### Dependencies
STP relies on : boost, flex, bison and minisat. You can install these by:

```
$ sudo apt-get install cmake bison flex libboost-all-dev python perl minisat
```

If your distribution does not come with minisat, STP maintains an updated fork. It can be built as follows:

```
$ git clone https://github.com/stp/minisat
$ cd minisat
$ mkdir build && cd build
$ cmake ..
$ cmake --build .
$ sudo cmake --install .
$ command -v ldconfig && sudo ldconfig
```

STP uses minisat as its SAT solver by default but it also supports other SAT solvers including CryptoMiniSat as an optional extra. If installed, it will be detected during the cmake and used:

```
$ git clone https://github.com/msoos/cryptominisat
$ cd cryptominisat
$ mkdir build && cd build
$ cmake ..
$ cmake --build .
$ sudo cmake --install .
$ command -v ldconfig && sudo ldconfig
```

Alternatively, these commands are pre-configured in `scripts/deps/setup-csb.sh`.  
After running the script, run `source ~/.bashrc` so CMake can locate the installed dependencies.

#### Building against non-installed libraries

If you wish to build STP's dependencies without installing them, you can tell CMake where to find the non-installed artefacts. For example:

* `-DMINISAT_INCLUDE_DIRS:PATH=<path>` and `-DMINISAT_LIBDIR:PATH=<path>` -- the paths to `minisat/core/Solver.h` and the `minisat` libraries (respectively)
* `-Dcryptominisat5_DIR:PATH=<path>` -- the path to `cryptominisat5Config.cmake`

If you did not install these development libraries, then `MINISAT_LIBDIR` can be set to your `build` folder for minisat and `cryptominisat5_DIR` to your `build` folder for CryptoMiniSat.

### Building a static library and binary

```
$ mkdir build && cd build
$ cmake -DSTATICCOMPILE=ON ..
$ cmake --build .
$ sudo cmake --install .
$ command -v ldconfig && sudo ldconfig
```

### Configuration and build options

To tweak the build configuration:

* Run `cmake-gui /path/to/stp/source/root` instead of `cmake`. This
  user interface lets you control the value of various configuration
  variables and lets you pick the build system generator.

* Run `ccmake` instead of `cmake`. This provides an ncurses terminal
  interface for changing configuration variables.

* Pass `-D<VARIABLE>=<VALUE>` options to `cmake` (not very user friendly).
  It is probably best if you **only** configure this way if you are writing
  scripts.

You can also tweak configuration later by running `make edit_cache` and edit any configuration variables, reconfigure and then regenerate the build system. After configuration, build by running `make`.

You can use the `-j<n>` flag to significantly to decrease build time by running `<n>` jobs in parallel (e.g. `make -j4`).

### Testing

```
git clone https://github.com/stp/stp
git submodule update --init
pip install lit
mkdir build
cd build
cmake -DENABLE_TESTING=ON ..
make
make test
```

### Installing

To install run `make install` and to uninstall run `make uninstall`. The root of installation is controlled by the `CMAKE_INSTALL_PREFIX` variable at configure time. You can change this by running `make edit_cache` and editing the value of `CMAKE_INSTALL_PREFIX`.


### Building on Windows/Visual Studio

You will need to install [cmake](https://cmake.org/download/) and follow the steps that AppVeyor [follows](https://github.com/stp/stp/blob/master/appveyor.yml). In case you need the static binary, you can always access it as a binary artifact at the [AppVeyor build page](https://ci.appveyor.com/project/msoos/stp). In case you still have trouble, please see the mini-HOWTO [at issue #319](https://github.com/stp/stp/issues/319).

### Building Docker

```
git clone https://github.com/stp/stp
cd stp
docker build -t stp .
echo "(set-logic QF_BV)
(assert (= (bvsdiv (_ bv3 2) (_ bv2 2)) (_ bv0 2)))
(check-sat)
(exit)" | docker run --rm -i stp
```

