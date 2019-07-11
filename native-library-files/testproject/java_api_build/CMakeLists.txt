cmake_minimum_required(VERSION 3.8.0)

project(foobarJ)

#SWIG - load the cmake package and add to include set
find_package(SWIG REQUIRED)
include(UseSWIG)

#JAVA & JNI - load the cmake package and add to include set
set(JAVA_AWT_INCLUDE_PATH NotNeeded)
find_package(Java REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

include_directories(${JNI_INCLUDE_DIRS}) # add jni to includes

# variable setups
set(FOOBAR_SWIG_INTERFACE foobarapi.i)
set(CMAKE_SWIG_OUTPUTDIR "swig_builds")

find_library(FOOBAR_RAW_LIB "foobar" PATHS "./lib" NO_DEFAULT_PATH )

# JAVA package
set(CMAKE_SWIG_FLAGS -package net.saheed.foobar)
set(CMAKE_SWIG_OUTDIR "net/saheed/foobar")
# therefore
set(JAVA_API_DIR "./build/net/saheed/foobar")

##################### END OF SET UP and VARIABLE SETTINGS ###############

### Build the project we are creating bindings for - FooBar => as a shared library
include_directories("../FooBar/include/") #here lies FooBar.hpp

### USING SWIG: Build the C/C++ code into a library, accessed via our defined interface (in SWIG) 

# we are using C++
set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate a interface to interact with the earlier created library
swig_add_library(foobarapi SHARED
			LANGUAGE Java
			SOURCES ${FOOBAR_SWIG_INTERFACE}
		)

# here we link the library and the api we  created for it together
swig_link_libraries(foobarapi PUBLIC ${FOOBAR_RAW_LIB})

set_property(TARGET foobarapi PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

### END of Build the Shared Library API

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

#set(CMAKE_JAVA_JAR_ENTRY_POINT main)
#add_jar(
#    Main
#    SOURCES main.java
#    ENTRY_POINT main
#)
#add_dependencies( Main FoobarJavaAPI )
