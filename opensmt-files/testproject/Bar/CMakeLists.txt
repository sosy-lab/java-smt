add_library(Bar "")
target_sources(Bar
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include/bar/Bar.hpp>
    $<INSTALL_INTERFACE:include/bar/Bar.hpp>
  PRIVATE
    src/Bar.cpp
)
target_include_directories(Bar
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)
set_target_properties(Bar PROPERTIES
  VERSION ${PROJECT_VERSION}
  PUBLIC_HEADER $<TARGET_PROPERTY:Bar,INTERFACE_SOURCES>
)
#target_link_libraries(Bar PUBLIC ...)
add_library(CMakeSwig::Bar ALIAS Bar)

# Install
include(GNUInstallDirs)
install(TARGETS Bar
  EXPORT CMakeSwigTargets
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/bar
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  #RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
