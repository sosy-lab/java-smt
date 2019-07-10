cmake_minimum_required(VERSION 3.8.0)

project(foobarapp)

#allow gdb to run on the shared object; required for debugging.
set(CMAKE BUILD TYPE Debug)

#SWIG - load the cmake package and add to include set
find_package(SWIG REQUIRED)
include(UseSWIG)

#JAVA & JNI - load the cmake package and add to include set
set(JAVA_AWT_INCLUDE_PATH NotNeeded)
find_package(Java REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

# variable setups
set(FOOBAR_SWIG_INTERFACE foobarapi.i)
set(CMAKE_SWIG_OUTPUTDIR @{CMAKE_CURRENT_BINARY_DIR})

# JAVA package
set(CMAKE_SWIG_FLAGS -package net.saheed.foobar)
set(CMAKE_SWIG_OUTDIR "net/saheed/foobar")
# therefore
set(JAVA_API_DIR "./build/net/saheed/foobar")

##################### END OF SET UP and VARIABLE SETTINGS ###############

### Build the project we are creating bindings for - FooBar => as a shared library
include_directories("FooBar/src/include/") #here lies FooBar.hpp


## OPTION 1 - build the library with this CMakeFile and link it

#this generate the actual .so file for the project (all source file, so no separate .so)
#add_library(foobar SHARED ../FooBar/src/FooBar.cpp ../FooBar/src/include/FooBar.hpp
#                          ../Bar/src/Bar.cpp ../Bar/src/include/Bar.hpp
#                          ../Foo/src/Foo.cpp ../Foo/src/include/Foo.hpp
#)

## END OF OPTION 1

#this says where to put the generated .so relative to the directory "cmake" is executed from
#set_target_properties(foobar PROPERTIES_LIBRARY_OUTPUT_DIRECTORY ${PROJECT BINARY DIR}/..)


## OPTION 2 - call another CMakeFile to build the library and put the binaries here

add_subdirectory(./normal_build @{CMAKE_CURRENT_BINARY_DIR})

## END OF OPTION 2



### USING SWIG: Build the C/C++ code into a library, accessed via our defined interface (in SWIG) 

include_directories(${JNI_INCLUDE_DIRS}) # add jni to includes

# we are using C++
set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate a interface to interact with the earlier created library
swig_add_library(foobarapi SHARED
			LANGUAGE Java
			SOURCES ${FOOBAR_SWIG_INTERFACE}
		)

# here we link the library and the api we  created for it together
swig_link_libraries(foobarapi foobar)

set_property(TARGET foobarapi PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

### END of Build the Shared Library API

# For convenience we copy the built library to the current build folder
#add_custom_command( TARGET foobarapi POST_BUILD
#                    COMMAND ${CMAKE_COMMAND} -E 
#		    copy_if_different $<TARGET_FILE:foobarapi> ${CMAKE_CURRENT_BINARY_DIR} )


# Build the library API now in JAVA - FoobarJavaAPI.jar, linking the .so, and generated JNI java files
# For pyhton - swig_link_libraries(foobarPYapi foobarapi ${PYTHON_LIBRARIES} )
# For JAVA :

add_jar(
    FoobarJavaAPI
    SOURCES    ${JAVA_API_DIR}/foobarapi.java
    	       ${JAVA_API_DIR}/foobarapiJNI.java
)
add_dependencies( FoobarJavaAPI foobarapi )

# Finally build the demonstration code into Main.jar    - ToDo: Do this in Ant

set(CMAKE_JAVA_JAR_ENTRY_POINT main)
add_jar(
    Main
    SOURCES main.java
    ENTRY_POINT main
)
add_dependencies( Main FoobarJavaAPI )
