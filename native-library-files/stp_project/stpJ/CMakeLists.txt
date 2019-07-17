cmake_minimum_required(VERSION 3.8.0)

project(stpJ)

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
set(STP_SWIG_INTERFACE stpJapi.i)
set(CMAKE_SWIG_OUTPUTDIR "swig_builds")

# find_library(OPENSMT_RAW_LIB "opensmt2" PATHS "./lib" NO_DEFAULT_PATH )

set(STP_DIR "" CACHE PATH "Try to use particular STP install (set this to folder where STPConfig.cmake is installed)")
find_package(STP REQUIRED)
message("Using STP library rooted at ${STP_DIR}")

# Get full path to STP executable
get_target_property(STP_FULL_PATH ${STP_EXECUTABLE} LOCATION)
message("Full path to STP binary is ${STP_FULL_PATH}")



# JAVA package
set(CMAKE_SWIG_FLAGS -package org.sosy_lab.java_smt.native_api.stp)
set(CMAKE_SWIG_OUTDIR "org/sosy_lab/java_smt/native_api/stp")
# therefore
set(JAVA_API_DIR "build/org/sosy_lab/java_smt/native_api/stp")

##################### END OF SET UP and VARIABLE SETTINGS ###############

# /JavaSMT/native-library-files/opensmt2/opensmt/src/api
include_directories(${STP_INCLUDE_DIRS})

### USING SWIG: Build the C/C++ code into a library, accessed via our defined interface (in SWIG) 

# we are using C++
# set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate a interface to interact with the earlier created library
swig_add_library(stpJapi SHARED
			LANGUAGE Java
			SOURCES ${STP_SWIG_INTERFACE}
		)

# here we link the library and the api we  created for it together
swig_link_libraries(stpJapi PUBLIC stp)

set_property(TARGET stpJapi PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

### END of Build the Shared Library API

# Build the library API now in JAVA - opensmt2JavaAPI.jar, linking the .so, and generated JNI java files
# For pyhton - swig_link_libraries(foobarPYapi foobarapi ${PYTHON_LIBRARIES} )
# For JAVA :

add_jar(
    stpJavaAPI
    SOURCES    ${JAVA_API_DIR}/stpJapi.java
    	       ${JAVA_API_DIR}/stpJapiJNI.java
)
add_dependencies( stpJavaAPI stpJapi )
