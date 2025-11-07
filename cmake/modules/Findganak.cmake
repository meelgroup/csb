# ─────────────────────────────────────────────────────────────
# Findganak.cmake — locate Ganak from your local build only
# ─────────────────────────────────────────────────────────────

message(STATUS ">>> loading custom Findganak.cmake from ${CMAKE_CURRENT_LIST_FILE}")

# 1) Determine GANAK_ROOT (where ganak/build lives)
if(NOT DEFINED GANAK_ROOT)
  get_filename_component(_MODULE_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)
  # go up: Modules → cmake → csb (project root) → solvers → ganak/build
  set(GANAK_ROOT
      "${_MODULE_DIR}/../../../ganak/build"
      CACHE PATH "Path to your local Ganak build directory")
endif()
message(STATUS "    Ganak root: ${GANAK_ROOT}")

# 2) headers: look under <root>/include or <root>/include/ganak
find_path(GANAK_INCLUDE_DIRS
  NAMES ganak.hpp
  HINTS "${GANAK_ROOT}/include"
  PATH_SUFFIXES
    ""       # e.g. build/include
    ganak    # e.g. build/include/ganak
)

# 3) shared library: libganak.so
find_library(GANAK_SHARED_LIBRARIES
  NAMES ganak
  HINTS "${GANAK_ROOT}/lib"
)

# 4) static archive: libganak.a
find_file(GANAK_STATIC_LIBRARIES
  NAMES libganak.a
  HINTS "${GANAK_ROOT}/lib"
)

# 5) pick whichever we found
if(GANAK_SHARED_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_SHARED_LIBRARIES})
elseif(GANAK_STATIC_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_STATIC_LIBRARIES})
endif()

# 6) Ganak bundles CaDiCaL and CaDiBack.  Ganak's exported CMake
# configuration does not currently list these as link dependencies, so we
# discover them manually and append them to GANAK_LIBRARIES.  This mirrors the
# behaviour of Ganak's own build scripts and fixes missing linkage on macOS
# where the dynamic loader otherwise fails to locate libcadical / libcadiback.
set(_GANAK_DEP_SEARCH_DIRS)

if(GANAK_LIBRARIES)
  # Prefer to search next to the Ganak library we located.
  get_filename_component(_GANAK_LIB_DIR "${GANAK_LIBRARIES}" DIRECTORY)
  list(APPEND _GANAK_DEP_SEARCH_DIRS "${_GANAK_LIB_DIR}")
endif()

list(APPEND _GANAK_DEP_SEARCH_DIRS
  "${GANAK_ROOT}"
  "${GANAK_ROOT}/lib"
  "${GANAK_ROOT}/cadical"
  "${GANAK_ROOT}/cadical/build"
  "${GANAK_ROOT}/cadiback"
  "${GANAK_ROOT}/cadiback/build"
)

list(REMOVE_DUPLICATES _GANAK_DEP_SEARCH_DIRS)

find_library(GANAK_CADICAL_LIBRARY
  NAMES cadical
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

find_library(GANAK_CADIBACK_LIBRARY
  NAMES cadiback
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

if(GANAK_CADICAL_LIBRARY)
  list(APPEND GANAK_LIBRARIES ${GANAK_CADICAL_LIBRARY})
  message(STATUS "    Found CaDiCaL library for Ganak: ${GANAK_CADICAL_LIBRARY}")
else()
  message(WARNING "    Could not locate CaDiCaL library required by Ganak")
endif()

if(GANAK_CADIBACK_LIBRARY)
  list(APPEND GANAK_LIBRARIES ${GANAK_CADIBACK_LIBRARY})
  message(STATUS "    Found CaDiBack library for Ganak: ${GANAK_CADIBACK_LIBRARY}")
else()
  message(WARNING "    Could not locate CaDiBack library required by Ganak")
endif()

if(NOT GANAK_CADICAL_LIBRARY OR NOT GANAK_CADIBACK_LIBRARY)
  foreach(_ganak_dir IN LISTS _GANAK_DEP_SEARCH_DIRS)
    if(EXISTS "${_ganak_dir}")
      file(GLOB _ganak_dir_entries LIST_DIRECTORIES TRUE "${_ganak_dir}/*")
      if(_ganak_dir_entries)
        list(SORT _ganak_dir_entries)
        message(STATUS "    Contents of ${_ganak_dir}:")
        foreach(_ganak_entry IN LISTS _ganak_dir_entries)
          message(STATUS "      ${_ganak_entry}")
        endforeach()
      else()
        message(STATUS "    Directory ${_ganak_dir} exists but is empty")
      endif()
    endif()
  endforeach()
endif()

list(REMOVE_DUPLICATES GANAK_LIBRARIES)

unset(_GANAK_DEP_SEARCH_DIRS)
unset(_GANAK_LIB_DIR)


# 7) standard “not found” handling
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ganak
  REQUIRED_VARS GANAK_INCLUDE_DIRS GANAK_LIBRARIES
)

mark_as_advanced(
  GANAK_ROOT
  GANAK_INCLUDE_DIRS
  GANAK_SHARED_LIBRARIES
  GANAK_STATIC_LIBRARIES
  GANAK_CADICAL_LIBRARY
  GANAK_CADIBACK_LIBRARY
)
