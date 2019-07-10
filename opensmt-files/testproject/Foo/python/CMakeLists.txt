set_property(SOURCE foo.i PROPERTY CPLUSPLUS ON)
set_property(SOURCE foo.i PROPERTY SWIG_MODULE_NAME pyFoo)
swig_add_library(pyFoo
	TYPE SHARED
	LANGUAGE python
	OUTPUT_DIR ${CMAKE_BINARY_DIR}/python/${PROJECT_NAME}/Foo
	SOURCES	foo.i)

target_include_directories(pyFoo
	PRIVATE
	../include
	${PYTHON_INCLUDE_DIRS}
	)
set_property(TARGET pyFoo PROPERTY SWIG_USE_TARGET_INCLUDE_DIRECTORIES ON)

# note: macOS is APPLE and also UNIX !
if(APPLE)
	set_target_properties(pyFoo PROPERTIES
		SUFFIX ".so"
		INSTALL_RPATH	"@loader_path;@loader_path/../../${PROJECT_NAME}/.libs"
		)
	set_property(TARGET pyFoo APPEND PROPERTY
		LINK_FLAGS "-flat_namespace -undefined suppress"
		)
elseif(UNIX)
	set_target_properties(pyFoo PROPERTIES
    INSTALL_RPATH	"$ORIGIN:$ORIGIN/../../${PROJECT_NAME}/.libs"
		)
endif()

target_link_libraries(pyFoo
	PRIVATE
	Foo
	${PYTHON_LIBRARIES}
	)
