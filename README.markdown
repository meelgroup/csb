[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![Linux Build](https://github.com/meelgroup/csb/actions/workflows/ci.yml/badge.svg)
<!-- [![Linux build](https://travis-ci.org/meelgroup/csb.svg?branch=main)](https://travis-ci.org/meelgroup/csb) -->

<!-- [![Windows build](https://ci.appveyor.com/api/projects/status/35983b7cnrg37whk?svg=true)](https://ci.appveyor.com/project/msoos/stp) -->
<!-- [![Documentation](https://readthedocs.org/projects/stp/badge/?version=latest)](https://stp.readthedocs.io/en/latest/?*badge*=latest) -->
<!-- [![Coverity](https://scan.coverity.com/projects/861/badge.svg)](https://scan.coverity.com/projects/861) -->
<!-- [![Codacy Badge](https://api.codacy.com/project/badge/Grade/f043efa22ea64e9ba44fde0f3a4fb09f)](https://www.codacy.com/app/soos.mate/cryptominisat?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=msoos/cryptominisat&amp;utm_campaign=Badge_Grade) -->

# CSB

CSB (Count and Sample on Bitvectors) is an approximate model counting and almost-uniform sampling tool aimed at solving constraints of bitvectors.

To learn more about CSB, please have a look at our [SMT Workshop '24 paper](https://ceur-ws.org/Vol-3725/short2.pdf).

CSB uses [STP](https://github.com/stp/stp) as its frontend and is built on top of that. For counting it uses [ApproxMC](https://github.com/meelgroup/approxmc) (with [Arjun](https://github.com/meelgroup/arjun)). For sampling, it uses [UniGen](https://github.com/meelgroup/unigen/).

## Build and install

For a quick install:

```
sudo apt install git cmake bison flex libboost-all-dev python3 perl build-essential python3-distutils-extra zlib1g-dev libboost-program-options-dev libboost-serialization-dev libgmp-dev libmpfr-dev
git clone https://github.com/meelgroup/csb
cd csb
./scripts/deps/setup-staticdeps.sh
mkdir build && cd build
cmake -DSTATICCOMPILE=ON ..
cmake --build .
```


## Usage

### Usage as Uniform-like Sampler:
The samples should be uniform in practice. Run with an SMT-LIB2 file:

```
./csb -s --ns 10 --seed 6 myproblem.smt2
```


### Usage as Almost-uniform Sampler:

The samples are generated with theoretical guarantees on uniformity. But this procedure might be slower than uniform-like sampler.
```
./csb -u --ns 10 --seed 6 myproblem.smt2
```

Change seed value to get different samples. Refer to [this post](https://www.msoos.org/2022/06/checking-uniform-like-samplers/) to know more about uniform, almost-uniform and uniform like samplers.

### Usage as Approximate Counter:

Run with an SMT-LIB2 file:
```
./csb -c myproblem.smt2
```

## Input format

The [SMT-LIB2](https://smtlib.cs.uiowa.edu/language.shtml) format is the recommended file format, because it is parsed by all modern bitvector solvers. Only quantifier-free bitvectors and arrays are implemented from the SMT-LIB2 format.

### Support for Projection Variables
CSB supports projection variables for counting and sampling. Variables can be designated as projection variables using the `proj-var` keyword. Each `proj-var` command can include one or more variables and multiple `proj-var` commands are supported. Projection variables can be declared at any point in the file, provided they are specified after the variable declaration and before the `proj-var` command. Here is an example of extending the SMT-LIB2 format to include projection variables.
```
(set-logic QF_BV)

(declare-const a (_ BitVec 6))
(declare-const b (_ BitVec 6))
(declare-const c (_ BitVec 6))
(declare-const d (_ BitVec 6))

(proj-var a b)
(proj-var d)

(assert (bvult a #b001010))
(assert (bvult b #b011110))
(assert (= (bvadd c d) #b001000))

(check-sat)
```

## Architecture

**CSB** converts bitvector constraints into SAT using [STP](https://github.com/stp/stp), integrating with [ApproxMC](https://github.com/meelgroup/approxmc) or [UniGen](https://github.com/meelgroup/unigen/) based on specific needs of counting or sampling. The benchmarks used for evaluating CSB in the SMT workshop paper are available [here](https://utoronto-my.sharepoint.com/:u:/g/personal/arijit_shaw_mail_utoronto_ca/EWcTcfGobH5Jl5SwjzRu6TQB169vWwTnjg-IXWiHJwmuDA?e=MFuxUM).


# Authors

* [Arijit Shaw](https://arijitsh.github.io)
* [Kuldeep S. Meel](https://www.cs.toronto.edu/~meel/)

Please refer to  STP/UniGen/ApproxMC for the respective authors.

