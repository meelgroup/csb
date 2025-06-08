message(STATUS ">>> loading custom Findapproxmc.cmake from ${CMAKE_CURRENT_LIST_FILE}")

# 1) Determine APPROXMC_ROOT (where approxmc/build lives)
if(NOT DEFINED APPROXMC_ROOT)
  get_filename_component(_MODULE_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)
  # go up: Modules → cmake → csb (project root) → solvers → approxmc/build
  set(APPROXMC_ROOT
      "${_MODULE_DIR}/../../../approxmc/build"
      CACHE PATH "Path to your local ApproxMC build directory")
endif()
message(STATUS "    ApproxMC root: ${APPROXMC_ROOT}")

# 2) headers: look under <root>/include or <root>/include/approxmc
find_path(APPROXMC_INCLUDE_DIRS
  NAMES
    approxmc.h
    approxmc.hpp
  HINTS
    "${APPROXMC_ROOT}/include"
  PATH_SUFFIXES
    ""           # e.g. build/include
    approxmc     # e.g. build/include/approxmc
)

# 3) shared library: libapproxmc.so
find_library(APPROXMC_SHARED_LIBRARIES
  NAMES approxmc
  HINTS "${APPROXMC_ROOT}/lib"
)

# 4) static archive: libapproxmc.a
find_file(APPROXMC_STATIC_LIBRARIES
  NAMES libapproxmc.a
  HINTS "${APPROXMC_ROOT}/lib"
)

# 5) pick the one we found
if(APPROXMC_SHARED_LIBRARIES)
  set(APPROXMC_LIBRARIES ${APPROXMC_SHARED_LIBRARIES})
elseif(APPROXMC_STATIC_LIBRARIES)
  set(APPROXMC_LIBRARIES ${APPROXMC_STATIC_LIBRARIES})
endif()

# 6) standard “not found” handling
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(approxmc
  REQUIRED_VARS APPROXMC_INCLUDE_DIRS APPROXMC_LIBRARIES
)

mark_as_advanced(
  APPROXMC_ROOT
  APPROXMC_INCLUDE_DIRS
  APPROXMC_SHARED_LIBRARIES
  APPROXMC_STATIC_LIBRARIES
)