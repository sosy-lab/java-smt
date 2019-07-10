# Setup SWIG
find_package(SWIG REQUIRED)
include(UseSWIG)

set(ASSEMBLY_NAME Mizux.CMakeSwig.FooBar)
# Detect Runtime IDentifier
if(UNIX)
  if(NOT APPLE)
    set(RID linux-x64)
    set(SWIG_LIB .so)
  else()
    set(RID osx-x64)
    set(SWIG_LIB .dylib)
  endif()
else()
  set(RID win-x64)
  set(SWIG_LIB .dll)
endif()
set(RUNTIME_FOOBAR runtime.${RID}.${ASSEMBLY_NAME})

set_property(SOURCE foobar.i PROPERTY CPLUSPLUS ON)
include_directories(../include)
list(APPEND CMAKE_SWIG_FLAGS "-namespace;${ASSEMBLY_NAME}")
#set(CMAKE_SWIG_OUTDIR ${CMAKE_CURRENT_BINARY_DIR}/..)

# this will generate ${RUNTIME_FOOBAR}.cs AND _%module%.so
set(UseSWIG_TARGET_NAME_PREFERENCE LEGACY)
swig_add_library(${RUNTIME_FOOBAR}
	TYPE SHARED
	LANGUAGE csharp
	SOURCES	foobar.i)

target_link_libraries(${SWIG_MODULE_${RUNTIME_FOOBAR}_REAL_NAME}
  PRIVATE CMakeSwig::FooBar)
if(UNIX)
	if(NOT APPLE)
    set_target_properties(${SWIG_MODULE_${RUNTIME_FOOBAR}_REAL_NAME} PROPERTIES
			INSTALL_RPATH	"$ORIGIN")
	else()
    set_target_properties(${SWIG_MODULE_${RUNTIME_FOOBAR}_REAL_NAME} PROPERTIES
			INSTALL_RPATH	"@loader_path")
    set_property(TARGET ${SWIG_MODULE_${RUNTIME_FOOBAR}_REAL_NAME} APPEND PROPERTY
			LINK_FLAGS "-flat_namespace -undefined suppress")
	endif()
endif()
