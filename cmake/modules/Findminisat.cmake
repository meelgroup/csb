# - Try to find minisat
# Once done this will define
#  MINISAT_FOUND - System has minisat
#  MINISAT_INCLUDE_DIRS - The minisat include directories
#  MINISAT_LIBRARIES - The libraries needed to use minisat
#  MINISAT_DEFINITIONS - Compiler switches required for using minisat

find_package(PkgConfig)
pkg_check_modules(PC_MINISAT QUIET minisat)
set(MINISAT_DEFINITIONS ${PC_LIBXML_CFLAGS_OTHER})

find_path(MINISAT_INCLUDE_DIR minisat/core/Solver.h
          HINTS ${MINISAT_INCLUDE_DIRS}
          PATH_SUFFIXES minisat minisat2 )

find_library(MINISAT_LIBRARY NAMES minisat minisat2
             HINTS ${MINISAT_LIBDIR} ${MINISAT_LIBRARY_DIRS} )

set(MINISAT_LIBRARIES ${MINISAT_LIBRARY} )
set(MINISAT_INCLUDE_DIRS ${MINISAT_INCLUDE_DIR} )

include(FindPackageHandleStandardArgs)
# handle the QUIETLY and REQUIRED arguments and set MINISAT_FOUND to TRUE
# if all listed variables are TRUE
find_package_handle_standard_args(minisat  DEFAULT_MSG
                                  MINISAT_LIBRARY MINISAT_INCLUDE_DIR)

mark_as_advanced(MINISAT_INCLUDE_DIR MINISAT_LIBRARY )
