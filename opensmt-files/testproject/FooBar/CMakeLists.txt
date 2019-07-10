add_library(FooBar "")
target_sources(FooBar
  PUBLIC
	  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include/foobar/FooBar.hpp>
	  $<INSTALL_INTERFACE:include/foobar/FooBar.hpp>
  PRIVATE
  src/FooBar.cpp
)
target_include_directories(FooBar
  PUBLIC
	  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
	  $<INSTALL_INTERFACE:include>
)
set_target_properties(FooBar PROPERTIES
  VERSION ${PROJECT_VERSION}
  PUBLIC_HEADER $<TARGET_PROPERTY:FooBar,INTERFACE_SOURCES>
)
# note: macOS is APPLE and also UNIX !
if(APPLE)
  set_target_properties(FooBar PROPERTIES
		INSTALL_RPATH "@loader_path")
elseif(UNIX)
  set_target_properties(FooBar PROPERTIES
		INSTALL_RPATH "$ORIGIN")
endif()
target_link_libraries(FooBar
  PUBLIC
    CMakeSwig::Foo
    CMakeSwig::Bar
)
add_library(CMakeSwig::FooBar ALIAS FooBar)

# Install
include(GNUInstallDirs)
install(TARGETS FooBar
	EXPORT CMakeSwigTargets
	PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/foobar
	ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
	LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
	#RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
