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

# 5) cadiback dependency – required by ganak at runtime
find_library(CADIBACK_LIBRARY
  NAMES cadiback
  HINTS "${GANAK_ROOT}/lib"
)

if(CADIBACK_LIBRARY)
  # ganak uses the linux-style .so soname even on macOS. When the
  # dependency is provided as a .dylib the runtime linker cannot find the
  # requested libcadiback.so, so create a compatibility symlink next to
  # the dylib. This mirrors what happens on Linux where the real file is
  # already named libcadiback.so.
  if(APPLE AND CADIBACK_LIBRARY MATCHES "\\.dylib$")
    get_filename_component(_cadiback_dir "${CADIBACK_LIBRARY}" DIRECTORY)
    set(_cadiback_soname "${_cadiback_dir}/libcadiback.so")
    if(NOT EXISTS "${_cadiback_soname}")
      execute_process(
        COMMAND "${CMAKE_COMMAND}" -E create_symlink
                "${CADIBACK_LIBRARY}" "${_cadiback_soname}"
      )
    endif()
  endif()
endif()

# 6) pick whichever we found
if(GANAK_SHARED_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_SHARED_LIBRARIES})
elseif(GANAK_STATIC_LIBRARIES)
  set(GANAK_LIBRARIES ${GANAK_STATIC_LIBRARIES})
endif()

if(CADIBACK_LIBRARY)
  list(APPEND GANAK_LIBRARIES ${CADIBACK_LIBRARY})
endif()

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
)
