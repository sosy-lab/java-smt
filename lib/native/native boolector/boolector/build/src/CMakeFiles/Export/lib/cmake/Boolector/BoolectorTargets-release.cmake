#----------------------------------------------------------------
# Generated CMake target import file for configuration "Release".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "Boolector::boolector" for configuration "Release"
set_property(TARGET Boolector::boolector APPEND PROPERTY IMPORTED_CONFIGURATIONS RELEASE)
set_target_properties(Boolector::boolector PROPERTIES
  IMPORTED_LOCATION_RELEASE "${_IMPORT_PREFIX}/lib/libboolector.so"
  IMPORTED_SONAME_RELEASE "libboolector.so"
  )

list(APPEND _IMPORT_CHECK_TARGETS Boolector::boolector )
list(APPEND _IMPORT_CHECK_FILES_FOR_Boolector::boolector "${_IMPORT_PREFIX}/lib/libboolector.so" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
