cmake_minimum_required(VERSION 3.8.0)

project(opensmt2java)

######### SETUP--


#allow gdb to run on the shared object; required for debugging.
#set(CMAKE BUILD TYPE Debug)

#SWIG - load the cmake package and add to include set
find_package(SWIG REQUIRED)
include(UseSWIG)

#JAVA & JNI - load the cmake package and add to include set
set(JAVA_AWT_INCLUDE_PATH NotNeeded)
find_package(Java REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

# JNI includes
include_directories(${JNI_INCLUDE_DIRS})


# variable setups
set(OPENSMTJAVA_SWIG_INTERFACE opensmt2java.i)
set(CMAKE_SWIG_OUTPUTDIR cmake_swig_output)

# JAVA package
set(CMAKE_SWIG_FLAGS -package org.sosy_lab.java_smt.solvers.opensmt2)
set(CMAKE_SWIG_OUTDIR "org/sosy_lab/java_smt/solvers/opensmt2")
# therefore
set(JAVA_API_DIR "${CMAKE_CURRENT_BINARY_DIR}/org/sosy_lab/java_smt/solvers/opensmt2")

##################### END OF SET UP and VARIABLE SETTINGS ###############

message(CMAKE_BINARY_DIR: ${CMAKE_BINARY_DIR})
message(CMAKE_CURRENT_BINARY_DIR: ${CMAKE_CURRENT_BINARY_DIR}) 
message(JAVA_API_DIR: ${JAVA_API_DIR}) 

# opensmt2 includes
include_directories("${CMAKE_CURRENT_BINARY_DIR}/opensmt/src/api/") #here lies opensmt_c.h


# check if openSMT is not built already
#if(NOT EXISTS ${CMAKE_CURRENT_BINARY_DIR}/opensmt2build)
if(NOT EXISTS ${CMAKE_CURRENT_BINARY_DIR}/testprojectbuild)
  message(NOTE: "I could not find opensmt build folder so I am rebuilding it ...")

  #build the cloned openSMT into a directory here
  add_subdirectory(./opensmt opensmt2build)

 # add_subdirectory(./testproject testproject)

#elseif(<condition>)
#  <commands>

else()
  message("opensmt build folder found, skipping build")

endif()


set(OPENSMT2_RAW_LIB ${CMAKE_CURRENT_BINARY_DIR}/opensmt2build/src/api/libopensmt2.so) #opensmt2 shared library

# build our own API binding to the openSMT2 library built above

# if we are using C++
#set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate codes and a new library to interface with the openSMT2 library
swig_add_library(opensmt2api SHARED
			LANGUAGE Java
			SOURCES ${OPENSMTJAVA_SWIG_INTERFACE}
		)

# here we link the library and the api we  created for it together
swig_link_libraries(opensmt2api ${OPENSMT2_RAW_LIB})

target_include_directories(opensmt2api PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/opensmt2build/src/api)
#set_property(TARGET opensmt2api PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

### END of Build the Shared Library API


# Build the generated codes into a JAR, linking the .so, and generated JNI java files
# For pyhton - swig_link_libraries(foobarPYapi foobarapi ${PYTHON_LIBRARIES} )
# For JAVA :

add_jar(
    opensmt2JavaAPI
    SOURCES    ${JAVA_API_DIR}/opensmt2java.java
    	       ${JAVA_API_DIR}/opensmt2javaJNI.java
)
add_dependencies( opensmt2JavaAPI opensmt2api )


message(STATUS "----- finished -----")
