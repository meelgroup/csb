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

get_filename_component(_GANAK_SUPER_ROOT "${GANAK_ROOT}" DIRECTORY)

list(APPEND _GANAK_DEP_SEARCH_DIRS
  "${GANAK_ROOT}"
  "${GANAK_ROOT}/lib"
  "${GANAK_ROOT}/cadical"
  "${GANAK_ROOT}/cadical/build"
  "${GANAK_ROOT}/cadical/build/lib"
  "${GANAK_ROOT}/cadiback"
  "${GANAK_ROOT}/cadiback/build"
  "${GANAK_ROOT}/cadiback/lib"
  "${_GANAK_SUPER_ROOT}"
  "${_GANAK_SUPER_ROOT}/cadical"
  "${_GANAK_SUPER_ROOT}/cadical/build"
  "${_GANAK_SUPER_ROOT}/cadiback"
  "${_GANAK_SUPER_ROOT}/cadiback/build"
)

list(REMOVE_DUPLICATES _GANAK_DEP_SEARCH_DIRS)

message(STATUS "    Ganak dependency search directories:")
foreach(_ganak_dir IN LISTS _GANAK_DEP_SEARCH_DIRS)
  message(STATUS "      ${_ganak_dir}")
endforeach()

set(_GANAK_DIRS_TO_LOG)
foreach(_ganak_dir IN LISTS _GANAK_DEP_SEARCH_DIRS)
  if(_ganak_dir MATCHES "cadical" OR _ganak_dir MATCHES "cadiback")
    list(APPEND _GANAK_DIRS_TO_LOG "${_ganak_dir}")
  endif()
endforeach()
if(GANAK_LIBRARIES)
  get_filename_component(_GANAK_LIB_DIR "${GANAK_LIBRARIES}" DIRECTORY)
  list(APPEND _GANAK_DIRS_TO_LOG "${_GANAK_LIB_DIR}")
endif()
list(REMOVE_DUPLICATES _GANAK_DIRS_TO_LOG)

foreach(_ganak_dir IN LISTS _GANAK_DIRS_TO_LOG)
  if(EXISTS "${_ganak_dir}")
    file(GLOB _ganak_dir_entries LIST_DIRECTORIES TRUE "${_ganak_dir}/*")
    list(SORT _ganak_dir_entries)
    message(STATUS "    Contents of ${_ganak_dir}:")
    if(_ganak_dir_entries)
      foreach(_ganak_entry IN LISTS _ganak_dir_entries)
        message(STATUS "      ${_ganak_entry}")
      endforeach()
    else()
      message(STATUS "      (empty)")
    endif()
    unset(_ganak_dir_entries)
  endif()
endforeach()
unset(_GANAK_DIRS_TO_LOG)

find_library(GANAK_CADICAL_SHARED_LIBRARY
  NAMES cadical
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

find_file(GANAK_CADICAL_STATIC_LIBRARY
  NAMES libcadical.a
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

find_library(GANAK_CADIBACK_SHARED_LIBRARY
  NAMES cadiback
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

find_file(GANAK_CADIBACK_STATIC_LIBRARY
  NAMES libcadiback.a
  HINTS ${_GANAK_DEP_SEARCH_DIRS}
)

set(GANAK_CADICAL_LIBRARY "")
set(_GANAK_CADICAL_CANDIDATES)
if(APPLE)
  list(APPEND _GANAK_CADICAL_CANDIDATES
    ${GANAK_CADICAL_STATIC_LIBRARY}
    ${GANAK_CADICAL_SHARED_LIBRARY})
else()
  list(APPEND _GANAK_CADICAL_CANDIDATES
    ${GANAK_CADICAL_SHARED_LIBRARY}
    ${GANAK_CADICAL_STATIC_LIBRARY})
endif()
foreach(_candidate IN LISTS _GANAK_CADICAL_CANDIDATES)
  if(_candidate)
    set(GANAK_CADICAL_LIBRARY "${_candidate}")
    break()
  endif()
endforeach()
unset(_GANAK_CADICAL_CANDIDATES)

set(GANAK_CADIBACK_LIBRARY "")
set(_GANAK_CADIBACK_CANDIDATES)
if(APPLE)
  list(APPEND _GANAK_CADIBACK_CANDIDATES
    ${GANAK_CADIBACK_STATIC_LIBRARY}
    ${GANAK_CADIBACK_SHARED_LIBRARY})
else()
  list(APPEND _GANAK_CADIBACK_CANDIDATES
    ${GANAK_CADIBACK_SHARED_LIBRARY}
    ${GANAK_CADIBACK_STATIC_LIBRARY})
endif()
foreach(_candidate IN LISTS _GANAK_CADIBACK_CANDIDATES)
  if(_candidate)
    set(GANAK_CADIBACK_LIBRARY "${_candidate}")
    break()
  endif()
endforeach()
unset(_GANAK_CADIBACK_CANDIDATES)

if(GANAK_CADICAL_LIBRARY)
  list(APPEND GANAK_LIBRARIES ${GANAK_CADICAL_LIBRARY})
  if(GANAK_CADICAL_STATIC_LIBRARY AND GANAK_CADICAL_LIBRARY STREQUAL GANAK_CADICAL_STATIC_LIBRARY)
    set(_ganak_cadical_kind "static")
  elseif(GANAK_CADICAL_SHARED_LIBRARY AND GANAK_CADICAL_LIBRARY STREQUAL GANAK_CADICAL_SHARED_LIBRARY)
    set(_ganak_cadical_kind "shared")
  else()
    set(_ganak_cadical_kind "unknown type")
  endif()
  message(STATUS "    Using CaDiCaL ${_ganak_cadical_kind} library for Ganak: ${GANAK_CADICAL_LIBRARY}")
  unset(_ganak_cadical_kind)
else()
  message(WARNING "    Could not locate CaDiCaL library required by Ganak")
endif()

if(GANAK_CADIBACK_LIBRARY)
  list(APPEND GANAK_LIBRARIES ${GANAK_CADIBACK_LIBRARY})
  if(GANAK_CADIBACK_STATIC_LIBRARY AND GANAK_CADIBACK_LIBRARY STREQUAL GANAK_CADIBACK_STATIC_LIBRARY)
    set(_ganak_cadiback_kind "static")
  elseif(GANAK_CADIBACK_SHARED_LIBRARY AND GANAK_CADIBACK_LIBRARY STREQUAL GANAK_CADIBACK_SHARED_LIBRARY)
    set(_ganak_cadiback_kind "shared")
  else()
    set(_ganak_cadiback_kind "unknown type")
  endif()
  message(STATUS "    Using CaDiBack ${_ganak_cadiback_kind} library for Ganak: ${GANAK_CADIBACK_LIBRARY}")
  unset(_ganak_cadiback_kind)
else()
  message(WARNING "    Could not locate CaDiBack library required by Ganak")
endif()

if(NOT GANAK_CADICAL_LIBRARY OR NOT GANAK_CADIBACK_LIBRARY)
  message(STATUS "    Ganak dependency directories still missing libraries; additional search roots:")
  foreach(_ganak_dir IN LISTS _GANAK_DEP_SEARCH_DIRS)
    if(_ganak_dir MATCHES "cadical" OR _ganak_dir MATCHES "cadiback")
      continue()
    endif()
    if(EXISTS "${_ganak_dir}")
      file(GLOB _ganak_dir_entries LIST_DIRECTORIES TRUE "${_ganak_dir}/*")
      list(SORT _ganak_dir_entries)
      message(STATUS "      ${_ganak_dir}")
      if(_ganak_dir_entries)
        foreach(_ganak_entry IN LISTS _ganak_dir_entries)
          message(STATUS "        ${_ganak_entry}")
        endforeach()
      else()
        message(STATUS "        (empty)")
      endif()
      unset(_ganak_dir_entries)
    endif()
  endforeach()
endif()

list(REMOVE_DUPLICATES GANAK_LIBRARIES)

unset(_GANAK_DEP_SEARCH_DIRS)
unset(_GANAK_LIB_DIR)
unset(_GANAK_SUPER_ROOT)


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
  GANAK_CADICAL_SHARED_LIBRARY
  GANAK_CADICAL_STATIC_LIBRARY
  GANAK_CADIBACK_LIBRARY
  GANAK_CADIBACK_SHARED_LIBRARY
  GANAK_CADIBACK_STATIC_LIBRARY
)
