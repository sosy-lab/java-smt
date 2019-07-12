cmake_minimum_required(VERSION 3.8.0)

project(opensmt2J)

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
set(OPENSMT_SWIG_INTERFACE opensmt2Japi.i)
set(CMAKE_SWIG_OUTPUTDIR "swig_builds")

find_library(OPENSMT_RAW_LIB "opensmt2" PATHS "./lib" NO_DEFAULT_PATH )

# JAVA package
set(CMAKE_SWIG_FLAGS -package org.sosy_lab.java_smt)
set(CMAKE_SWIG_OUTDIR "org/sosy_lab/java_smt")
# therefore
set(JAVA_API_DIR "build/org/sosy_lab/java_smt")

##################### END OF SET UP and VARIABLE SETTINGS ###############

# /JavaSMT/native-library-files/opensmt2/opensmt/src/api
include_directories("../opensmt/src/api/") #here lies opensmt_c.h


### USING SWIG: Build the C/C++ code into a library, accessed via our defined interface (in SWIG) 

# we are using C++
# set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate a interface to interact with the earlier created library
swig_add_library(opensmt2api SHARED
			LANGUAGE Java
			SOURCES ${OPENSMT_SWIG_INTERFACE}
		)

# here we link the library and the api we  created for it together
swig_link_libraries(opensmt2api PUBLIC ${OPENSMT_RAW_LIB})

set_property(TARGET opensmt2api PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

### END of Build the Shared Library API

# Build the library API now in JAVA - opensmt2JavaAPI.jar, linking the .so, and generated JNI java files
# For pyhton - swig_link_libraries(foobarPYapi foobarapi ${PYTHON_LIBRARIES} )
# For JAVA :

add_jar(
    opensmt2JavaAPI
    SOURCES    ${JAVA_API_DIR}/opensmt2Japi.java
    	       ${JAVA_API_DIR}/opensmt2JapiJNI.java
)
add_dependencies( opensmt2JavaAPI opensmt2api )
