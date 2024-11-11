# AUTHORS: Dan Liew, Ryan Gvostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

set(sat_lib_to_add
    MinisatCore.cpp
    SimplifyingMinisat.cpp
)

if (USE_CRYPTOMINISAT)
    include_directories(${CRYPTOMINISAT5_INCLUDE_DIRS})
    message(STATUS "Including CryptoMiniSat")
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat5.cpp)
endif()

if (USE_UNIGEN)
    include_directories(${UNIGEN_INCLUDE_DIRS})
    include_directories(${APPROXMC_INCLUDE_DIRS})
    include_directories(${CMSGEN_INCLUDE_DIRS})
    include_directories(${ARJUN_INCLUDE_DIRS})
    message(STATUS "Including ApproxMC, CMSGen and UniGen")
    set(sat_lib_to_add ${sat_lib_to_add} ApxMC.cpp)
    set(sat_lib_to_add ${sat_lib_to_add} UniSamp.cpp)
    set(sat_lib_to_add ${sat_lib_to_add} CMSGen.cpp)
endif()

if (USE_RISS)
    set(sat_lib_to_add ${sat_lib_to_add} RissCore.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

