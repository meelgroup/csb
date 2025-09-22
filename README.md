[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
<!-- [![Linux build](https://travis-ci.org/stp/stp.svg?branch=master)](https://travis-ci.org/stp/stp) -->
<!-- [![Windows build](https://ci.appveyor.com/api/projects/status/35983b7cnrg37whk?svg=true)](https://ci.appveyor.com/project/msoos/stp) -->
<!-- [![Documentation](https://readthedocs.org/projects/stp/badge/?version=latest)](https://stp.readthedocs.io/en/latest/?badge=latest) -->
<!-- [![Coverity](https://scan.coverity.com/projects/861/badge.svg)](https://scan.coverity.com/projects/861) -->
<!-- [![Codacy Badge](https://api.codacy.com/project/badge/Grade/f043efa22ea64e9ba44fde0f3a4fb09f)](https://www.codacy.com/app/soos.mate/cryptominisat?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=msoos/cryptominisat&amp;utm_campaign=Badge_Grade) -->

# CSB

CSB (Count and Sample on Bitvectors) is an exact / approximate model counting and almost-uniform sampling tool aimed at solving constraints of bitvectors. CSB supports *projection* and *weighted model counting*.

To learn more about CSB, please have a look at our [SMT Workshop '24 paper](https://ceur-ws.org/Vol-3725/short2.pdf).

CSB uses [STP](https://github.com/stp/stp) as its frontend and is built on top of that. For counting it uses [ApproxMC](https://github.com/meelgroup/approxmc) (with [Arjun](https://github.com/meelgroup/arjun)). For sampling, it uses [UniGen](https://github.com/meelgroup/unigen/).


## Building

### Use Release Binaries
Use of the [release binaries](https://github.com/meelgroup/csb/releases) is
_strongly_ encouraged, as CSB requires a specific set of libraries to be
installed. The second best thing to use is Nix.
<!-- ```shell
nix shell github:meelgroup/ganak#ganak
``` -->

### Building with Nix
 Simply [install nix](https://nixos.org/download/), then build  `csb`:
```
nix --extra-experimental-features 'nix-command flakes' shell github:meelgroup/csb#csb
```

The resulting binaries and libraries are exposed under the `result` symlink created by
the build.
Then you will have `csb` binary available and ready to use.

If you want to build manually on MacOS or Linux, see the [build.md](https://github.com/meelgroup/csb/blob/main/scripts/build.md) file for detailed instructions.

<!--
See the [GitHub
Action](https://github.com/meelgroup/csb/actions/workflows/build.yml) for the
specific set of steps. -->


## Usage

The [SMT-LIB2](https://smtlib.cs.uiowa.edu/language.shtml) format is the recommended file format, because it is parsed by all modern bitvector solvers. Only quantifier-free bitvectors and arrays are implemented from the SMT-LIB2 format.


### Usage as Exact Counter (Weighted/Unweighted):

Run with an SMT-LIB2 file:
```
./csb myproblem.smt2
```


### Usage as Approximate Counter:

Run with an SMT-LIB2 file:
```
./csb -a myproblem.smt2
```

### Usage as Uniform-like Sampler:
The samples should be uniform in practice. Run with an SMT-LIB2 file:

```
./csb -s -n 10 myproblem.smt2
```


### Usage as Almost-uniform Sampler:

The samples are generated with theoretical guarantees on uniformity. But this procedure might be slower than uniform-like sampler.
```
./csb -u -n 10 myproblem.smt2
```

Change seed value to get different samples. Refer to [this post](https://www.msoos.org/2022/06/checking-uniform-like-samplers/) to know more about uniform, almost-uniform and uniform like samplers.

### Get model preserving bitblasted CNF:
```
./csb -c myproblem.smt2
```



## Input format

The [SMT-LIB2](https://smtlib.cs.uiowa.edu/language.shtml) format is the recommended file format, because it is parsed by all modern bitvector solvers. Only quantifier-free bitvectors and arrays are implemented from the SMT-LIB2 format.

### Support for Projection Variables
CSB supports projection variables for counting and sampling. Variables can be designated as projection variables using the `declare-projvar` keyword. Each `declare-projvar` command can include one or more variables and multiple `declare-projvar` commands are supported. Projection variables can be declared at any point in the file, provided they are specified after the variable declaration and before the `declare-projvar` command. Here is an example of extending the SMT-LIB2 format to include projection variables.
```
(set-logic QF_BV)

(declare-const a (_ BitVec 6))
(declare-const b (_ BitVec 6))
(declare-const c (_ BitVec 6))
(declare-const d (_ BitVec 6))

(declare-projvar a b)
(declare-projvar d)

(assert (bvult a #b001010))
(assert (bvult b #b011110))
(assert (= (bvadd c d) #b001000))

(check-sat)
```

### Support for Weights

CSB supports weights for variables in the counting process. Weights can be assigned to each variable (and its negation) using the `declare-weight` keyword. Weights can be assigned to Boolean variables only. Here is an example of extending the SMT-LIB2 format to include weights.
```
(set-logic QF_BV)

(declare-const p Bool)
(declare-const q Bool)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))

(declare-weight p 0.8)
(declare-weight -p 1.0)
(declare-weight q 0.3)

; If p then x+y = 10, if q then x+y = 5 (mod 16).
(assert (=> p (= (bvadd x y) #xA))) ; 0x0A = 10
(assert (=> q (= (bvadd x y) #x5))) ; 0x05 = 5

(check-sat)
```
You can add weights to both literals of a variable. If only one literal is given a weight `w`, the other literal is assigned a default weight of `(1.0-w)`. If no weights are provided for a projection variable, both literals are assigned a default weight of `0.5`.



## Architecture

**CSB** converts bitvector constraints into SAT using [STP](https://github.com/stp/stp), integrating with [Ganak](https://github.com/meelgroup/ganak), [ApproxMC](https://github.com/meelgroup/approxmc), [CMSGen](https://github.com/meelgroup/cmsgen), [UniGen](https://github.com/meelgroup/unigen/) based on specific needs of counting or sampling. The benchmarks used for evaluating CSB in the SMT workshop paper are available [here](https://utoronto-my.sharepoint.com/:u:/g/personal/arijit_shaw_mail_utoronto_ca/EWcTcfGobH5Jl5SwjzRu6TQB169vWwTnjg-IXWiHJwmuDA?e=MFuxUM).


# Authors

* [Arijit Shaw](https://arijitsh.github.io)
* [Kuldeep S. Meel](https://www.cs.toronto.edu/~meel/)

Please refer to  STP/Ganak/UniGen/ApproxMC/CMSGen for the respective authors.

