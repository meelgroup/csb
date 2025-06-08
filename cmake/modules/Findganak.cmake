# cmake/Modules/Findganak.cmake
message(STATUS ">>> loading custom Findganak.cmake from ${CMAKE_CURRENT_LIST_FILE}")

set(_PREFIXES
  ${CMAKE_PREFIX_PATH}      # respects -DCMAKE_PREFIX_PATH
  /usr/local                # your install prefix
  /opt/ganak
)

# 1) headers: look for ganak.hpp in <prefix>/include/ganak
find_path(GANAK_INCLUDE_DIRS
  NAMES    ganak.hpp
  HINTS    ${_PREFIXES}
  PATH_SUFFIXES
    include
    include/ganak
)

# 2) shared lib
find_library(GANAK_SHARED_LIBRARIES
  NAMES ganak
  HINTS ${_PREFIXES}
  PATH_SUFFIXES lib
)

# 3) static archive
find_file(GANAK_STATIC_LIBRARIES
  NAMES libganak.a
  HINTS ${_PREFIXES}
  PATH_SUFFIXES lib
)

# pick whichever we found
if(GANAK_SHARED_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_SHARED_LIBRARIES})
elseif(GANAK_STATIC_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_STATIC_LIBRARIES})
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ganak
  REQUIRED_VARS GANAK_INCLUDE_DIRS GANAK_LIBRARIES
)

mark_as_advanced(
  GANAK_INCLUDE_DIRS
  GANAK_SHARED_LIBRARIES
  GANAK_STATIC_LIBRARIES
)
