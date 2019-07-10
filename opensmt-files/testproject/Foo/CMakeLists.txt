add_library(Foo "")
target_sources(Foo
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include/foo/Foo.hpp>
    $<INSTALL_INTERFACE:include/foo/Foo.hpp>
  PRIVATE
    src/Foo.cpp
)
target_include_directories(Foo
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)
set_target_properties(Foo PROPERTIES
  VERSION ${PROJECT_VERSION}
  PUBLIC_HEADER $<TARGET_PROPERTY:Foo,INTERFACE_SOURCES>
)
#target_link_libraries(Foo PUBLIC ...)
add_library(CMakeSwig::Foo ALIAS Foo)

# Install
include(GNUInstallDirs)
install(TARGETS Foo
  EXPORT CMakeSwigTargets
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/foo
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  #RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
