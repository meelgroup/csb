# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
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

cmake_minimum_required(VERSION 3.5 FATAL_ERROR)

if(POLICY CMP0048)
    #policy for VERSION in cmake 3.0
    cmake_policy(SET CMP0048 NEW)
endif()

if(POLICY CMP0074)
    #policy for <PackageName>_ROOT variables
    cmake_policy(SET CMP0074 NEW)
endif()

if(POLICY CMP0092)
    # Disable passing /W3 by default on MSVC
    cmake_policy(SET CMP0092 NEW)
endif()

if(POLICY CMP0077)
    # Allow to override options via regular variables
    cmake_policy(SET CMP0077 NEW)
endif()

project(CSB)

set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

include(GenerateExportHeader)
include(GNUInstallDirs)
include(FeatureSummary)

# Search paths for custom CMake modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/modules)

# Search for packages in the deps directory
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/install")
message(STATUS "CMAKE_MODULE_PATH = ${CMAKE_MODULE_PATH}")

# Automatically ensure git submodules are present so a fresh clone can be
# configured and built in a single step.
if (EXISTS "${PROJECT_SOURCE_DIR}/.git")
    find_package(Git QUIET)
    if (GIT_FOUND)
        execute_process(
            COMMAND ${GIT_EXECUTABLE} submodule update --init
            WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
            RESULT_VARIABLE GIT_SUBMOD_RESULT
            OUTPUT_VARIABLE GIT_SUBMOD_STDOUT
            ERROR_VARIABLE GIT_SUBMOD_STDERR
            OUTPUT_STRIP_TRAILING_WHITESPACE
            ERROR_STRIP_TRAILING_WHITESPACE
        )

        if (NOT GIT_SUBMOD_RESULT EQUAL 0)
            message(FATAL_ERROR "Failed to update git submodules: ${GIT_SUBMOD_STDERR}")
        elseif (GIT_SUBMOD_STDOUT)
            message(STATUS "Git submodules updated: ${GIT_SUBMOD_STDOUT}")
        else()
            message(STATUS "Git submodules already up to date")
        endif()
    else()
        message(WARNING "Git not found; skipping automatic submodule update.")
    endif()
endif()

# generate JSON file of compile commands -- useful for code extension
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

set(INCLUDEDIR include CACHE STRING "Output directory for include headers")
set(STP_TIMESTAMPS ON CACHE BOOL "Enable build with timestamps")

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)

      message(STATUS "You can choose the type of build, options are: ${build_types}")
      set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
          "Options are ${build_types}"
          FORCE
         )

      # Provide drop down menu options in cmake-gui
      set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Option to enable/disable assertions
# -----------------------------------------------------------------------------

# Filter out definition of NDEBUG from the default build configuration flags.
# We will add this ourselves if we want to disable assertions
foreach (build_config ${build_types})
    string(TOUPPER ${build_config} upper_case_build_config)
    foreach (language CXX C)
        set(VAR_TO_MODIFY "CMAKE_${language}_FLAGS_${upper_case_build_config}")
        string(REGEX REPLACE "(^| )[/-]D *NDEBUG($| )"
                             " "
                             replacement
                             "${${VAR_TO_MODIFY}}"
              )
        #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
        set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
    endforeach()
endforeach()

option(ENABLE_ASSERTIONS "Build with assertions enabled" ON)
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(ENABLE_ASSERTIONS OFF)
endif()

if (ENABLE_ASSERTIONS)
    # NDEBUG was already removed.
else()
    # Note this definition doesn't appear in the cache variables.
    add_definitions(-DNDEBUG)
endif()
add_feature_info(Assertions ENABLE_ASSERTIONS "Enables assertions")

# -----------------------------------------------------------------------------
# Enable LLVM sanitizations.
# Note that check_cxx_compiler_flag doesn't work, a fix is needed here
# -----------------------------------------------------------------------------
macro(add_cxx_flag flagname)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
endmacro()

include(MacroPushRequiredVars)

option(SANITIZE "Use Clang sanitizers" OFF)
if (SANITIZE)
    # Set in Cache so user can tweak it later
    SET(CMAKE_CXX_COMPILER "clang++" CACHE FILEPATH "" FORCE)
    message(STATUS "Forcing compiler: ${CMAKE_CXX_COMPILER}")
    add_cxx_flag("-fsanitize=return")
    add_cxx_flag("-fsanitize=bounds")
    add_cxx_flag("-fsanitize=integer")
    add_cxx_flag("-fsanitize=undefined")
    add_cxx_flag("-fsanitize=float-divide-by-zero")
    add_cxx_flag("-fsanitize=integer-divide-by-zero")
    add_cxx_flag("-fsanitize=null")
    add_cxx_flag("-fsanitize=unsigned-integer-overflow")
    add_cxx_flag("-fsanitize=address")
    add_cxx_flag("-Wno-bitfield-constant-conversion")
endif()
add_feature_info(Sanitizers SANITIZE "Enables Clang sanitizers, will force using clang++ as the compiler")

# -----------------------------------------------------------------------------
# Let the user decide if they want to build shared or static client library.
# STP will link against this client library
# -----------------------------------------------------------------------------

option(BUILD_SHARED_LIBS "Build the shared library" OFF)
option(STATICCOMPILE "Compile static library and executable" ON)
if (STATICCOMPILE)
    set(BUILD_SHARED_LIBS OFF)
    set(ENABLE_PYTHON_INTERFACE OFF)
endif()
add_feature_info(Static STATICCOMPILE "Compiles static library and executable")

if ((${CMAKE_SYSTEM_NAME} MATCHES "Windows") OR (NOT BUILD_SHARED_LIBS))
    set(Boost_USE_STATIC_LIBS ON)
    set(Minisat_USE_STATIC_LIBS ON)
endif()

if (NOT BUILD_SHARED_LIBS)
    if (NOT MSVC)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -Wl,--whole-archive -lpthread -Wl,--no-whole-archive -static ")
        set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")

        # removing -rdynamic that's automatically added
        foreach (language CXX C)
            set(VAR_TO_MODIFY "CMAKE_SHARED_LIBRARY_LINK_${language}_FLAGS")
            string(REGEX REPLACE "(^| )-rdynamic($| )"
                                 " "
                                 replacement
                                 "${${VAR_TO_MODIFY}}")
            #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
            set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
        endforeach()
    endif()
else ()
    # use, i.e. don't skip the full RPATH for the build tree
    SET(CMAKE_SKIP_BUILD_RPATH  FALSE)

    # when building, don't use the install RPATH already
    # (but later on when installing)
    SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)

    SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_LIBDIR}")

    # add the automatically determined parts of the RPATH
    # which point to directories outside the build tree to the install RPATH
    SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

    # the RPATH to be used when installing, but only if it's not a system directory
    LIST(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_LIBDIR}" isSystemDir)
    IF("${isSystemDir}" STREQUAL "-1")
        SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_LIBDIR}")
    ENDIF("${isSystemDir}" STREQUAL "-1")

    if (APPLE)
      set(CMAKE_MACOSX_RPATH ON)
      set(CMAKE_INSTALL_RPATH "@loader_path/../lib")
      message(STATUS "Using RPATH for dynamic linking")
    endif()
endif()

option(SUPPRESS_WARNINGS "Silence all warnings" OFF)

if (NOT MSVC)
    add_compile_options( -g)
    add_compile_options( -pthread )

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:-O2>")

    add_compile_options("$<$<CONFIG:RELEASE>:-O2>")
    add_compile_options("$<$<CONFIG:RELEASE>:-g0>")

    add_compile_options("$<$<CONFIG:DEBUG>:-O0>")

    if(NOT CMAKE_BUILD_TYPE STREQUAL "Debug")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -O2")
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -O2")
    endif()
else()
    # see https://msdn.microsoft.com/en-us/library/fwkeyyhe.aspx for details
    # /ZI = include debug info
    # /Wall = all warnings

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/O2>")
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/ZI>")

    add_compile_options("$<$<CONFIG:RELEASE>:/O2>")
    add_compile_options("$<$<CONFIG:RELEASE>:/D>")
    add_compile_options("$<$<CONFIG:RELEASE>:/NDEBUG>")

    add_compile_options("$<$<CONFIG:DEBUG>:/Od>")

    if (NOT BUILD_SHARED_LIBS)
        # We statically link to reduce dependencies
        foreach(flag_var CMAKE_CXX_FLAGS CMAKE_CXX_FLAGS_DEBUG CMAKE_CXX_FLAGS_RELEASE CMAKE_CXX_FLAGS_MINSIZEREL CMAKE_CXX_FLAGS_RELWITHDEBINFO)
            # /MD -- Causes the application to use the multithread-specific
            #        and DLL-specific version of the run-time library.
            #        Defines _MT and _DLL and causes the compiler to place
            #        the library name MSVCRT.lib into the .obj file.
            if(${flag_var} MATCHES "/MD")
                string(REGEX REPLACE "/MD" "/MT" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MD")

            # /MDd	-- Defines _DEBUG, _MT, and _DLL and causes the application to use the debug multithread-specific and DLL-specific version of the run-time library.
            #          It also causes the compiler to place the library name MSVCRTD.lib into the .obj file.
            if(${flag_var} MATCHES "/MDd")
                string(REGEX REPLACE "/MDd" "/MTd" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MDd")
        endforeach(flag_var)

        # Creates a multithreaded executable (static) file using LIBCMT.lib.
        add_compile_options(/MT)
    endif()

    # buffers security check
    add_compile_options(/GS)

    # Proper warning level
    if(SUPPRESS_WARNINGS)
        add_compile_options(/W0)
    else()
        add_compile_options(/W1)
    endif()

    # Disable STL used in DLL-boundary warning
    add_compile_options(/wd4251)
    add_compile_options(/D_CRT_SECURE_NO_WARNINGS)

    # Wall is MSVC's Weverything, so annoying unless used from the start
    # and with judiciously used warning disables
    # add_compile_options(/Wall)

    # /Za = only ansi C98 & C++11
    # /Za is not recommended for use, not tested, etc.
    # see: http://stackoverflow.com/questions/5489326/za-compiler-directive-does-not-compile-system-headers-in-vs2010
    # add_compile_options(/Za)

    add_compile_options(/fp:precise)

    # exception handling. s = The exception-handling model that catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" may throw an exception.
    # exception handling. c = If used with s (/EHsc), catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" never throw a C++ exception.
    add_compile_options(/EHsc)


    # set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /INCREMENTAL:NO")
    # set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /PDBCOMPRESS")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:1572864")

    #what does this do?
    set(DEF_INSTALL_CMAKE_DIR CMake)


    if (MSVC)
        # Windows compatibility includes
        set(STP_DEFS_COMM ${STP_DEFS_COMM} -D_CRT_SECURE_NO_WARNINGS)
        set(STP_INCL_COMM windows/winports windows/winports/msc99hdr ${STP_INCL_COMM})
        include_directories(${STP_INCL_COMM})
        add_subdirectory(windows)
        set(PLATFORM_COMPAT_LIBRARIES ${PLATFORM_COMPAT_LIBRARIES} windows_compat)
        set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

        # stack size of MSVC must be specified
        string(REGEX REPLACE "/STACK:[0-9]+" "" CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:512000000")

        # inline is not a keyword in visual studios old C version, allow its redefinition
        add_definitions("-D_ALLOW_KEYWORD_MACROS")
    endif()

endif()

# -----------------------------------------------------------------------------
# Set the appropriate build flags
# -----------------------------------------------------------------------------
include(CheckCXXCompilerFlag)

macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
  endif()
endmacro()

check_cxx_compiler_flag("-std=c++11" HAVE_FLAG_STD_CPP11)

if(APPLE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif()

if(NOT MSVC)
    if(SUPPRESS_WARNINGS)
        add_cxx_flag_if_supported("-w")
    else()
        add_cxx_flag_if_supported("-Wall")
        add_cxx_flag_if_supported("-Wextra")
        add_cxx_flag_if_supported("-Wunused")
        add_cxx_flag_if_supported("-pedantic")
        add_cxx_flag_if_supported("-Wsign-compare")
        add_cxx_flag_if_supported("-Wtype-limits")
        add_cxx_flag_if_supported("-Wuninitialized")
        add_cxx_flag_if_supported("-Wno-deprecated")
        add_cxx_flag_if_supported("-Wstrict-aliasing")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wheader-guard")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wformat-nonliteral")
        add_cxx_flag_if_supported("-Winit-self")
        add_cxx_flag_if_supported("-Wparentheses")
        add_cxx_flag_if_supported("-Wunreachable-code")
    endif()

    if (NOT CMAKE_BUILD_TYPE STREQUAL "Release")
        add_cxx_flag_if_supported("-fno-omit-frame-pointer")
    endif()
    #if(NOT ENABLE_TESTING AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        # almost working
        # add_cxx_flag_if_supported("-fvisibility=hidden")
        set(CMAKE_EXE_LINKER_FLAGS " ${CMAKE_EXE_LINKER_FLAGS} -Wl,--discard-all -Wl,--build-id=sha1")
    endif()
    # add_cxx_flag_if_supported("-flto") # slow compile and not enough benefits
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
endif()

add_definitions("-D__STDC_LIMIT_MACROS")

option(TUNE_NATIVE "Use -mtune=native" OFF)
if(TUNE_NATIVE)
  add_cxx_flag_if_supported("-mtune=native")
endif()

option(COVERAGE "Build with coverage check" OFF)
if (COVERAGE)
    add_cxx_flag("--coverage")
endif()

option(WERROR "Build with warnings as errors" OFF)
if (WERROR)
    if (NOT MSVC)
        message(STATUS "Enabling treating warnings as errors")
        # Let's make things be errors -- we can't test for this
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror")
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Werror")
    else()
        message(STATUS "Warnings as errors is not enabled under MSVC")
    endif()
endif()

option(USE_THREAD_LOCAL "Use thread-local storage when available" ON)
add_feature_info(ThreadLocal USE_THREAD_LOCAL "Enables use of thread-local storage when available")

if(WIN32)
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(BISON_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(PERL_PATH_HINT "C:/Perl/bin" CACHE STRING "Perl path hints, can be null if on your pat")

  set(PHINTS ${PERL_PATH_HINT} ${FLEX_PATH_HINT} ${BISON_PATH_HINT})
  add_definitions(${STP_DEFS_COMM})
endif()

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
function(SetVersionNumber PREFIX VERSION_MAJOR VERSION_MINOR VERSION_PATCH)
  set(${PREFIX}_VERSION_MAJOR ${VERSION_MAJOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_MINOR ${VERSION_MINOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_PATCH ${VERSION_PATCH} PARENT_SCOPE)
  set(${PREFIX}_VERSION
        "${VERSION_MAJOR}.${VERSION_MINOR}.${VERSION_PATCH}"
        PARENT_SCOPE)
endfunction()

find_program (GIT_EXECUTABLE git)
if (GIT_EXECUTABLE)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA)
  MESSAGE(STATUS "GIT hash found: ${GIT_SHA}")
else()
  set(GIT_SHA "GIT-hash-notfound")
endif()
set(STP_FULL_VERSION "2.3.3")

string(REPLACE "." ";" STP_FULL_VERSION_LIST ${STP_FULL_VERSION})
SetVersionNumber("PROJECT" ${STP_FULL_VERSION_LIST})
MESSAGE(STATUS "PROJECT_VERSION: ${PROJECT_VERSION}")
MESSAGE(STATUS "PROJECT_VERSION_MAJOR: ${PROJECT_VERSION_MAJOR}")
MESSAGE(STATUS "PROJECT_VERSION_MINOR: ${PROJECT_VERSION_MINOR}")
MESSAGE(STATUS "PROJECT_VERSION_PATCH: ${PROJECT_VERSION_PATCH}")

# -----------------------------------------------------------------------------
# Write out the config.h
# -----------------------------------------------------------------------------

configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/include/stp/config.h.in"
  "${CMAKE_CURRENT_BINARY_DIR}/include/stp/config.h"
)

# -----------------------------------------------------------------------------
# Set up includes
# -----------------------------------------------------------------------------
include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories("${CMAKE_CURRENT_BINARY_DIR}/include")

# FIXME: External library includes
include_directories(# For extlib-abc and extlib-constbv
                    ${PROJECT_SOURCE_DIR}/lib
                   )

find_package(Boost 1.46 COMPONENTS program_options REQUIRED)

# -----------------------------------------------------------------------------
# Find Riss
# -----------------------------------------------------------------------------
option(USE_RISS "Try to use Riss" OFF)
add_feature_info(Riss USE_RISS "Enables Riss solver")

if (USE_RISS)
    add_definitions(-DUSE_RISS)
    include_directories(${RISS_DIR}/)        # should point to the base directory: ~/git/riss/
    link_directories(${RISS_DIR}/build/lib)  # should point to the base directory: ~/git/riss/build/lib
endif()

# -----------------------------------------------------------------------------
# Find CryptoMiniSat
# -----------------------------------------------------------------------------
option(NOCRYPTOMINISAT "Don't try to use cryptominisat" ON)

if (NOT NOCRYPTOMINISAT)
  set(cryptominisat5_DIR "" CACHE PATH "Path to directory containing cryptominisat5Config.cmake")
  find_package(cryptominisat5 CONFIG)
  if (cryptominisat5_FOUND AND HAVE_FLAG_STD_CPP11 AND (NOT NOCRYPTOMINISAT))
    message(STATUS "CryptoMiniSat5 dynamic lib: ${CRYPTOMINISAT5_LIBRARIES}")
    message(STATUS "CryptoMiniSat5 static lib:  ${CRYPTOMINISAT5_STATIC_LIBRARIES}")
    message(STATUS "CryptoMiniSat5 static lib deps: ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS}")
    message(STATUS "CryptoMiniSat5 include dirs: ${CRYPTOMINISAT5_INCLUDE_DIRS}")
    add_definitions(-DUSE_CRYPTOMINISAT)
    set(USE_CRYPTOMINISAT ON)
    include_directories(SYSTEM ${CRYPTOMINISAT5_INCLUDE_DIRS})
  else()
  endif()
endif()
add_feature_info(CryptoMiniSat USE_CRYPTOMINISAT "Enables CryptoMiniSat solver, allows --cryptominisat5 option")

option(FORCE_CMS "Must build with CryptoMiniSat" OFF)
if (FORCE_CMS AND NOT USE_CRYPTOMINISAT)
    message(FATAL_ERROR "CryptoMiniSat 5.x was not found but it was requested. Exiting.")
endif()

# -----------------------------------------------------------------------------
# Find UniGen
# -----------------------------------------------------------------------------
set(USE_UNIGEN OFF)
option(NOUNIGEN "Don't try to use UniSamp" ON)

if (NOT NOUNIGEN)
  # Try to locate UniGen in the repository's deps directory by default so
  # users don't need to specify -Dunigen_DIR on the command line.
  set(_unigen_config_hints
      "${PROJECT_SOURCE_DIR}/deps/unigen/build"
      "${PROJECT_SOURCE_DIR}/../unigen/build"
  )

  # If the caller hasn't provided a usable path to unigenConfig.cmake, try a
  # few sensible defaults.  This covers both the local "deps" layout and the
  # directory structure used in CI where UniGen is checked out next to the
  # project repository.
  if(NOT DEFINED unigen_DIR OR unigen_DIR STREQUAL "" OR
     NOT EXISTS "${unigen_DIR}/unigenConfig.cmake")
    foreach(_unigen_candidate IN LISTS _unigen_config_hints)
      if(EXISTS "${_unigen_candidate}/unigenConfig.cmake")
        set(unigen_DIR "${_unigen_candidate}" CACHE PATH
            "Path to directory containing unigenConfig.cmake" FORCE)
        break()
      endif()
    endforeach()
  endif()
  unset(_unigen_candidate)
  unset(_unigen_config_hints)

  find_package(arjun CONFIG)
  if (arjun_FOUND)
      message(STATUS "Found Arjun")
      message(STATUS "Arjun dynamic lib : ${ARJUN_LIBRARIES}")
      message(STATUS "Arjun include dirs: ${ARJUN_INCLUDE_DIRS}")
      include_directories(SYSTEM ${ARJUN_INCLUDE_DIRS})
  else()
      message(FATAL_ERROR "Cannot find Arjun. Please install it! Exiting.")
  endif()
  find_package(approxmc CONFIG REQUIRED)

    message(STATUS "Found approxmc")
    message(STATUS "ApproxMC dynamic lib: ${APPROXMC_LIBRARIES}")
    message(STATUS "ApproxMC static lib:  ${APPROXMC_STATIC_LIBRARIES}")
    message(STATUS "ApproxMC static lib deps: ${APPROXMC_STATIC_LIBRARIES_DEPS}")
    message(STATUS "ApproxMC include dirs: ${APPROXMC_INCLUDE_DIRS}")
    include_directories(SYSTEM ${APPROXMC_INCLUDE_DIRS})

  find_package(sbva CONFIG REQUIRED)
    message(STATUS "Found sbva")
    message(STATUS "sbva dynamic lib: ${SBVA_LIBRARIES}")
    message(STATUS "sbva static lib:  ${SBVA_STATIC_LIBRARIES}")
    message(STATUS "sbva static lib deps: ${SBVA_STATIC_LIBRARIES_DEPS}")
    message(STATUS "sbva include dirs: ${SBVA_INCLUDE_DIRS}")
    include_directories(SYSTEM ${SBVA_INCLUDE_DIRS})


  find_package(cmsgen CONFIG REQUIRED)
    message(STATUS "Found cmsgen")
    message(STATUS "CMSGen dynamic lib: ${CMSGEN_LIBRARIES}")
    message(STATUS "CMSGen static lib:  ${CMSGEN_STATIC_LIBRARIES}")
    message(STATUS "CMSGen static lib deps: ${CMSGEN_STATIC_LIBRARIES_DEPS}")
    message(STATUS "CMSGen include dirs: ${CMSGEN_INCLUDE_DIRS}")
    include_directories(SYSTEM ${CMSGEN_INCLUDE_DIRS})


  find_package(unigen CONFIG)
  if (unigen_FOUND AND HAVE_FLAG_STD_CPP11 AND (NOT NOUNIGEN))
    message(STATUS "UniGen dynamic lib: ${UNIGEN_LIBRARIES}")
    message(STATUS "UniGen static lib:  ${UNIGEN_STATIC_LIBRARIES}")
    message(STATUS "UniGen static lib deps: ${UNIGEN_STATIC_LIBRARIES_DEPS}")
    message(STATUS "UniGen include dirs: ${UNIGEN_INCLUDE_DIRS}")
    add_definitions(-DUSE_UNIGEN)
    set(USE_UNIGEN ON)
    include_directories(SYSTEM ${UNIGEN_INCLUDE_DIRS})
  else()
    message(STATUS "UniGen NOT found")
  endif()
endif()
add_feature_info(UniGen USE_UNIGEN "Enables Uniform Sampling, allows --unisamp option")

option(FORCE_UNIG "Must build with UniGen" OFF)
if (FORCE_UNIG AND NOT USE_UNIGEN)
    message(FATAL_ERROR "UniSamp was not found but it was requested. Exiting.")
endif()



set(USE_GANAK OFF)
option(NOGANAK "Don't try to use Ganak" ON)

# KCBox provides both approximate counting and sampling without the heavy
# external dependency chain. Enable it explicitly to avoid pulling in the
# other optional counters and samplers unless the user opts in via the
# command line.
option(ENABLE_KCBOX "Build KCBox counter/sampler integration" ON)
add_feature_info(KCBox ENABLE_KCBOX "Enables KCBox counter/sampler")
if (ENABLE_KCBOX)
    add_definitions(-DUSE_KCBOX)
    add_definitions(-DNBUILD)
    include_directories(${PROJECT_SOURCE_DIR}/lib/KCBox/src)
    include_directories(${PROJECT_SOURCE_DIR}/lib/KCBox/cadical/src)
    find_package(GMP REQUIRED)
    include_directories(${GMP_INCLUDE_DIR})

    include(ExternalProject)
    set(CADICAL_SOURCE_DIR ${PROJECT_SOURCE_DIR}/lib/KCBox/cadical)
    set(CADICAL_LIBRARY ${CADICAL_SOURCE_DIR}/build/libcadical.a)
    set(CADICAL_URL "https://github.com/arminbiere/cadical/archive/81de5d2b5c68727b4d183ec5ceb56561f1b3b6e1.tar.gz")
    ExternalProject_Add(cadical_ep
        PREFIX ${CMAKE_BINARY_DIR}/external/cadical
        URL ${CADICAL_URL}
        URL_HASH SHA256=35e0f6f6470c164a2fc4a241238d1a75def8b885b2dc938a8c36e87c03127126
        SOURCE_DIR ${CADICAL_SOURCE_DIR}
        DOWNLOAD_EXTRACT_TIMESTAMP TRUE
        BUILD_IN_SOURCE 1
        UPDATE_COMMAND ""
        CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CXXFLAGS=-fPIC ./configure --competition
        BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} -j
        INSTALL_COMMAND ""
        LOG_CONFIGURE 1
        LOG_BUILD 1
    )

    add_library(cadical STATIC IMPORTED GLOBAL)
    set_target_properties(cadical PROPERTIES IMPORTED_LOCATION ${CADICAL_LIBRARY})
    add_dependencies(cadical cadical_ep)
endif()

if(NOT NOGANAK)
    add_definitions(-DUSE_GANAK)
    set(USE_GANAK ON)
  add_feature_info(Ganak USE_GANAK "Enables Ganak Model Counter solver, allows --exactcount option")
  find_package(GMP REQUIRED)
find_package(MPFR REQUIRED)
MESSAGE(STATUS "MPFR include dir: ${MPFR_INCLUDE_DIR}")
MESSAGE(STATUS "MPFR lib dir: ${MPFR_LIBRARIES}")
MESSAGE(STATUS "GMP include dir: ${GMP_INCLUDE_DIR}")
MESSAGE(STATUS "GMP lib dir: ${GMP_LIBRARIES}")
  find_package(arjun CONFIG REQUIRED)
  if (arjun_FOUND)
      message(STATUS "Found Arjun library")
      message(STATUS "Arjun dynamic lib: ${ARJUN_LIBRARIES}")
      message(STATUS "Arjun include dirs: ${ARJUN_INCLUDE_DIRS}")
  else()
      message(WARNING "Cannot find Arjun libraries.")
  endif()
find_package(sbva CONFIG REQUIRED)
  if (sbva_FOUND)
      message(STATUS "Found sbva library")
      message(STATUS "sbva dynamic lib: ${SBVA_LIBRARIES}")
      message(STATUS "sbva include dirs: ${SBVA_INCLUDE_DIRS}")
  else()
      message(WARNING "Cannot find sbva libraries.")
  endif()
find_package(breakid CONFIG REQUIRED)
  if (breakid_FOUND)
      message(STATUS "Found BreakID library")
      message(STATUS "BreakID dynamic lib: ${BREAKID_LIBRARIES}")
      message(STATUS "BreakID include dirs: ${BREAKID_INCLUDE_DIRS}")
  else()
      message(WARNING "Cannot find BreakID libraries.")
  endif()
find_package(approxmc CONFIG REQUIRED)
  if (approxmc_FOUND)
      message(STATUS "Found approxmc library")
      message(STATUS "approxmc dynamic lib: ${APPROXMC_LIBRARIES}")
      message(STATUS "approxmc include dirs: ${APPROXMC_INCLUDE_DIRS}")
  else()
      message(WARNING "Cannot find Arjun libraries.")
  endif()
  find_package(ganak CONFIG REQUIRED)
  if (ganak_FOUND)
      message(STATUS "Found Ganak library")
      message(STATUS "Ganak dynamic lib: ${GANAK_LIBRARIES}")
      message(STATUS "Ganak static lib:  ${GANAK_STATIC_LIBRARIES}")
      message(STATUS "Ganak include dirs: ${GANAK_INCLUDE_DIRS}")
  else()
      message(WARNING "Cannot find Ganak libraries.")
  endif()
else()
    message(STATUS "Ganak NOT found")
endif()


# -----------------------------------------------------------------------------
# Find ZLIB (needed for MiniSat)
# yes, we need to include the zlib header location or STP will not build
# thanks to MiniSat include-ing it n the header
# -----------------------------------------------------------------------------
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    execute_process(
        COMMAND brew --prefix zlib
        RESULT_VARIABLE BREW_ZLIB
        OUTPUT_VARIABLE BREW_ZLIB_PREFIX
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_ZLIB EQUAL 0 AND EXISTS "${BREW_ZLIB_PREFIX}")
        message(STATUS "Found Zlib keg installed by Homebrew at ${BREW_ZLIB_PREFIX}")
        list(APPEND CMAKE_PREFIX_PATH "${BREW_ZLIB_PREFIX}")
    endif()
endif()
find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})
set(LIBS ${LIBS} ${ZLIB_LIBRARIES})
include_directories(${minisat_SOURCE_DIR})

# ----------
# manpage
# ----------
message(STATUS "Help2man manpage generation disabled")


# -----------------------------------------------------------------------------
# Find Minisat (fall back to the bundled KCBox copy when enabled)
# -----------------------------------------------------------------------------

if (ENABLE_KCBOX)
    set(minisat_FOUND ON)
    set(MINISAT_INCLUDE_DIRS ${PROJECT_SOURCE_DIR}/lib/KCBox CACHE PATH "Bundled minisat headers" FORCE)
    set(MINISAT_LIBRARIES "" CACHE STRING "Bundled minisat library" FORCE)
endif()

if (NOT minisat_FOUND)
    find_package(minisat)
    set(MINISAT_INCLUDE_DIR "" CACHE PATH "MiniSat include directory")
    set(MINISAT_LIBRARY "" CACHE PATH "MiniSat library directory")

    if (minisat_FOUND)
        message(STATUS "OK, found Minisat library under ${MINISAT_LIBRARIES} and Minisat include dirs under ${MINISAT_INCLUDE_DIRS}")
    else()
        message(STATUS "Not found using installed MiniSat, looking for built MiniSat")
        find_package(minisat CONFIG)

        if (minisat_FOUND)
            message(STATUS "OK, found Minisat library under ${MINISAT_LIBRARIES} and Minisat include dirs under ${MINISAT_INCLUDE_DIRS}")
        else()
            message(FATAL_ERROR "You must install minisat from https://github.com/stp/minisat")
        endif()
    endif()
endif()

include_directories(SYSTEM ${MINISAT_INCLUDE_DIRS})
set(LIBS ${LIBS} ${MINISAT_LIBRARIES})

# -----------------------------------------------------------------------------
# Find Parser and Lexer generators
# -----------------------------------------------------------------------------

# On macOS, search Homebrew for keg-only versions of Bison and Flex. Xcode does
# not provide new enough versions for us to use.
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    execute_process(
        COMMAND brew --prefix bison
        RESULT_VARIABLE BREW_BISON
        OUTPUT_VARIABLE BREW_BISON_PREFIX
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_BISON EQUAL 0 AND EXISTS "${BREW_BISON_PREFIX}")
        message(STATUS "Found Bison keg installed by Homebrew at ${BREW_BISON_PREFIX}")
        set(BISON_EXECUTABLE "${BREW_BISON_PREFIX}/bin/bison")
    endif()

    execute_process(
        COMMAND brew --prefix flex
        RESULT_VARIABLE BREW_FLEX
        OUTPUT_VARIABLE BREW_FLEX_PREFIX
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_FLEX EQUAL 0 AND EXISTS "${BREW_FLEX_PREFIX}")
        message(STATUS "Found Flex keg installed by Homebrew at ${BREW_FLEX_PREFIX}")
        set(FLEX_EXECUTABLE "${BREW_FLEX_PREFIX}/bin/flex")
    endif()
endif()


find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

if (BISON_VERSION VERSION_LESS "2.6")
    message(FATAL_ERROR "STP requires Bison 2.6 or newer")
endif()

# required for genkinds.pl and a few other scripts
find_package(Perl REQUIRED)

# -----------------------------------------------------------------------------
# Query definitions
# -----------------------------------------------------------------------------
get_directory_property( DirDefs DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
set(COMPILE_DEFINES)
foreach( d ${DirDefs} )
    # message( STATUS "Found Define: " ${d} )
    set(COMPILE_DEFINES "${COMPILE_DEFINES} -D${d}")
endforeach()
message(STATUS "All defines at startup: ${COMPILE_DEFINES}")

# -----------------------------------------------------------------------------
# Setup library build path (this is **not** the library install path)
# -----------------------------------------------------------------------------
if(WIN32)
  # Create a single bin/ output directory so that DLL files can be
  # readily found on DLL platforms.
  set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
endif()

if(DEFINED CMAKE_CONFIGURATION_TYPES)
  # Placing the binaries in ${CMAKE_*_OUTPUT_DIRECTORY} without regard to
  # the debug/release/... configuration. This is needed for build systems
  # where files for multiple configurations are kept within the same build
  # directory (eg. MSBuild), since some targets (e.g. python-interface-tests)
  # require the path to the stp library to be given in a configuration file.
  # Note: the paths could be determined in a cleaner fashion by using generator
  # expressions, which were used up to commit 1af1f5. However, that solution
  # was not feasible, since CMake versions provided by recent Debian versions
  # are buggy w.r.t. generator expressions.
  foreach(OUTPUTCONFIG ${CMAKE_CONFIGURATION_TYPES})
    string(TOUPPER ${OUTPUTCONFIG} OUTPUTCONFIG_UPPER)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_LIBRARY_OUTPUT_DIRECTORY})
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
  endforeach(OUTPUTCONFIG CMAKE_CONFIGURATION_TYPES)
else()
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
endif()

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(STP_EXPORT_NAME "STPTargets")

# -----------------------------------------------------------------------------
# Testing and Python interface options
# -----------------------------------------------------------------------------

option(ENABLE_TESTING "Enable testing" OFF)

# try finding python if the user did not explicitly said that
# he/she does not want python bindings
if((NOT DEFINED ENABLE_PYTHON_INTERFACE) OR ENABLE_PYTHON_INTERFACE)
    find_package (PythonInterp)
    if(PYTHON_EXECUTABLE AND BUILD_SHARED_LIBS)
        set(ENABLE_PYTHON_INTERFACE ON)
    else()
        set(ENABLE_PYTHON_INTERFACE OFF)
    endif()
endif()
add_feature_info(PythonInterface ENABLE_PYTHON_INTERFACE "Enables Python interface")

# -----------------------------------------------------------------------------
# Compile all subdirs
# -----------------------------------------------------------------------------

message(STATUS "Final CXX flags ${CMAKE_CXX_FLAGS}")

option(BUILD_EXECUTABLES "Build executables" ON)
add_subdirectory(lib)
add_subdirectory(tools)
add_subdirectory(bindings)
add_feature_info(Executables BUILD_EXECUTABLES "Enables executables compilation")

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  IMMEDIATE @ONLY
)

add_custom_target(uninstall
  COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
)

# -----------------------------------------------------------------------------
# Add tests if required
# -----------------------------------------------------------------------------

if(ENABLE_TESTING AND NOT PYTHON_EXECUTABLE)
    message(STATUS "Python interpreter cannot be found. Please install it to have the python interface and to enable testing")
    set(ENABLE_TESTING OFF)
endif()

if(ENABLE_TESTING)
    if (NOT BUILD_SHARED_LIBS)
        set(ENABLE_TESTING OFF)
    endif()
endif()

if(ENABLE_TESTING)
  enable_testing()
  set(UNIT_TEST_EXE_SUFFIX "Tests" CACHE STRING "Suffix for Unit test executable")
#   add_custom_target(check
#     COMMENT "top level target to invoke all other tests"
#   )

  add_subdirectory(tests)
endif()
add_feature_info(Tests ENABLE_TESTING "Enables tests")

# -----------------------------------------------------------------------------
# Print information about used features
# -----------------------------------------------------------------------------
feature_summary(WHAT ENABLED_FEATURES DISABLED_FEATURES)

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP in the build-tree
# -----------------------------------------------------------------------------
set(STP_TARGETS_FILENAME "STPTargets.cmake")
set(STP_CONFIG_FILENAME "STPConfig.cmake")
set(STP_CONFIG_VERSION_FILENAME "STPConfigVersion.cmake")

export(TARGETS stp
    FILE "${PROJECT_BINARY_DIR}/${STP_TARGETS_FILENAME}")

# Create STPConfig file
set(EXPORT_TYPE "Build-tree")
set(CONF_INCLUDE_DIRS "${PROJECT_BINARY_DIR}/include")
configure_file(scripts/legacy/STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_FILENAME}" @ONLY
)
configure_file(scripts/legacy/STPConfigVersion.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}" @ONLY
)

# Export this package to the CMake user package registry
# Now the user can just use find_package(STP) on their system
export(PACKAGE STP)


# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP that is installed.
# -----------------------------------------------------------------------------
if(WIN32 AND NOT CYGWIN)
  set(DEF_INSTALL_CMAKE_DIR CMake)
else()
  set(DEF_INSTALL_CMAKE_DIR ${CMAKE_INSTALL_LIBDIR}/cmake/STP)
endif()
set(STP_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
  "Installation directory for STP CMake files"
)

# Create STPConfig file
set(EXPORT_TYPE "installed")
set(CONF_INCLUDE_DIRS "${CMAKE_INSTALL_FULL_INCLUDEDIR}")
configure_file(scripts/legacy/STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}" @ONLY
)

install(FILES
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}"
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}"
  DESTINATION "${STP_INSTALL_CMAKE_DIR}"
)

# Install the export set for use with the install-tree
install(EXPORT ${STP_EXPORT_NAME} DESTINATION
  "${STP_INSTALL_CMAKE_DIR}"
)

