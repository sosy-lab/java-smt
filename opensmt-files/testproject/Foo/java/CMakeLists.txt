# Setup SWIG
find_package(SWIG REQUIRED)
include(UseSWIG)

# Find java
find_package(Java COMPONENTS Development REQUIRED)
find_package(JNI REQUIRED)

set(PACKAGE_NAME net.mizux.cmakeswig.foo)

set_property(SOURCE foo.i PROPERTY CPLUSPLUS ON)
include_directories(../include)
list(APPEND CMAKE_SWIG_FLAGS "-package;${PACKAGE_NAME}")
#set(CMAKE_SWIG_OUTDIR ${CMAKE_CURRENT_BINARY_DIR})

# this will generate net.mizux.foo.java AND _%module%.so
set(UseSWIG_TARGET_NAME_PREFERENCE LEGACY)
set(FOO_NAME foo_wrap_java)
swig_add_library(${FOO_NAME}
	TYPE SHARED
	LANGUAGE java
	SOURCES	foo.i)

target_include_directories(${SWIG_MODULE_${FOO_NAME}_REAL_NAME}
  PRIVATE CMakeSwig::Foo ${JNI_INCLUDE_DIRS})
if(UNIX)
	if(NOT APPLE)
    set_target_properties(${SWIG_MODULE_${FOO_NAME}_REAL_NAME} PROPERTIES
			INSTALL_RPATH	"$ORIGIN")
	else()
    set_target_properties(${SWIG_MODULE_${FOO_NAME}_REAL_NAME} PROPERTIES
			INSTALL_RPATH	"@loader_path")
    set_property(TARGET ${SWIG_MODULE_${FOO_NAME}_REAL_NAME} APPEND PROPERTY
			LINK_FLAGS "-flat_namespace -undefined suppress")
	endif()
endif()
