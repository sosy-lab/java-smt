set_property(SOURCE bar.i PROPERTY CPLUSPLUS ON)
set_property(SOURCE bar.i PROPERTY SWIG_MODULE_NAME pyBar)
swig_add_library(pyBar
	LANGUAGE python
	OUTPUT_DIR ${CMAKE_BINARY_DIR}/python/${PROJECT_NAME}/Bar
	SOURCES bar.i)
set_property(TARGET pyBar PROPERTY
	SWIG_USE_TARGET_INCLUDE_DIRECTORIES ON
	)
target_include_directories(pyBar
	PRIVATE
	../include
	${PYTHON_INCLUDE_DIRS}
	)
# note: macOS is APPLE and also UNIX !
if(APPLE)
	set_target_properties(pyBar PROPERTIES
		SUFFIX ".so"
		INSTALL_RPATH "@loader_path;@loader_path/../../${PROJECT_NAME}/.libs"
		)
	set_property(TARGET pyBar APPEND PROPERTY
		LINK_FLAGS "-flat_namespace -undefined suppress"
		)
elseif(UNIX)
	set_target_properties(pyBar PROPERTIES
		INSTALL_RPATH "$ORIGIN:$ORIGIN/../../${PROJECT_NAME}/.libs"
		)
endif()
target_link_libraries(pyBar
	PRIVATE
	Bar
	${PYTHON_LIBRARIES}
	)
