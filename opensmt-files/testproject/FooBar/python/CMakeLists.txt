set_property(SOURCE foobar.i PROPERTY CPLUSPLUS ON)
set_property(SOURCE foobar.i PROPERTY SWIG_MODULE_NAME pyFooBar)
swig_add_library(pyFooBar
	LANGUAGE python
	OUTPUT_DIR ${CMAKE_BINARY_DIR}/python/${PROJECT_NAME}/FooBar
	SOURCES foobar.i)
set_property(TARGET pyFooBar PROPERTY SWIG_USE_TARGET_INCLUDE_DIRECTORIES ON)
target_include_directories(pyFooBar
	PRIVATE
	../include
	${PYTHON_INCLUDE_DIRS}
	)
# note: macOS is APPLE and also UNIX !
if(APPLE)
	set_target_properties(pyFooBar PROPERTIES
		SUFFIX ".so"
		INSTALL_RPATH "@loader_path;@loader_path/../../${PROJECT_NAME}/.libs"
		)
	set_property(TARGET pyFooBar APPEND PROPERTY
		LINK_FLAGS "-flat_namespace -undefined suppress"
		)
elseif(UNIX)
	set_target_properties(pyFooBar PROPERTIES
		INSTALL_RPATH "$ORIGIN:$ORIGIN/../../${PROJECT_NAME}/.libs"
		)
endif()
target_link_libraries(pyFooBar
	PRIVATE
	FooBar
	${PYTHON_LIBRARIES}
	)
