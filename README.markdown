[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
<!-- [![Linux build](https://travis-ci.org/stp/stp.svg?branch=master)](https://travis-ci.org/stp/stp) -->
<!-- [![Windows build](https://ci.appveyor.com/api/projects/status/35983b7cnrg37whk?svg=true)](https://ci.appveyor.com/project/msoos/stp) -->
<!-- [![Documentation](https://readthedocs.org/projects/stp/badge/?version=latest)](https://stp.readthedocs.io/en/latest/?badge=latest) -->
<!-- [![Coverity](https://scan.coverity.com/projects/861/badge.svg)](https://scan.coverity.com/projects/861) -->
<!-- [![Codacy Badge](https://api.codacy.com/project/badge/Grade/f043efa22ea64e9ba44fde0f3a4fb09f)](https://www.codacy.com/app/soos.mate/cryptominisat?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=msoos/cryptominisat&amp;utm_campaign=Badge_Grade) -->

# CSB

CSB (Count and Sample on Bitvectors) is an approximate model counting and almost-uniform sampling tool aimed at solving constraints of bitvectors.

CSB uses [STP](https://github.com/stp/stp) as its frontend and is built on top of that. For counting it uses [ApproxMC](https://github.com/meelgroup/approxmc) (with [Arjun](https://github.com/meelgroup/arjun)). For sampling, it uses [UniSamp](https://www.cs.toronto.edu/~meel/Papers/lics22.pdf).

## Build and install

For a quick install:

```
sudo apt-get install git cmake bison flex libboost-all-dev python2 perl build-essential
sudo apt-get install zlib1g-dev libboost-program-options-dev libboost-serialization-dev
git clone https://github.com/meelgroup/csb
cd csb
git submodule init && git submodule update
./scripts/deps/setup-gtest.sh
./scripts/deps/setup-outputcheck.sh
./scripts/deps/setup-cms.sh
./scripts/deps/setup-minisat.sh
./scripts/deps/setup-unigen.sh
mkdir build
cd build
cmake ..
cmake --build .
sudo cmake --install .
```


## Input format

The [SMT-LIB2](https://smtlib.cs.uiowa.edu/language.shtml) format is the recommended file format, because it is parsed by all modern bitvector solvers. Only quantifier-free bitvectors and arrays are implemented from the SMT-LIB2 format.

### Usage as Almost-uniform Sampler:

Run with an SMT-LIB2 file:

```
./stp --unisamp --seed 6 myproblem.smt2
```

Change seed value to get different samples.

### Usage as Approximate Counter:

Run with an SMT-LIB2 file:
```
./stp --approxmc myproblem.smt2
```

### Python Interface for Almost-uniform Sampler:
```
In [1]: import stp
In [2]: a = stp.Solver()
In [3]: x = a.bitvec('x')
In [4]: y = a.bitvec('y')
In [5]: a.add(x + y < 20)
In [6]: a.add(x  > 10)
In [7]: a.add(y  > 10)
In [8]: a.useUnigen()
Out[8]: True
In [9]: a.check()
Out[9]: True
In [10]: a.model()
Out[10]: {'x': 2371135469, 'y': 1923831833}
```

### Python Interface for Approximate Counter:

```
In [8]: a.useApproxMC()
Out[8]: True
In [9]: a.count()
Out[9]: 180388626432
```

## Architecture

**CSB** converts bitvector constraints into SAT using [STP](https://github.com/stp/stp), integrating with [ApproxMC](https://github.com/meelgroup/approxmc) or [UniSamp](https://github.com/arijitsh/unigen/tree/unisamp) based on specific needs of counting or sampling. This tool is developed from a study on model counters and bitblasting tools, as detailed in [this study](https://arijitsh.github.io/papers/sharpsmt.pdf).



# Authors

* Arijit Shaw
* Kuldeep S. Meel

Please refer to  STP/UniSamp/ApproxMC for the respective authors.

