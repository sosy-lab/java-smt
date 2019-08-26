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

set(RAW_LIB_DIR "./install_include/usr/local/lib")

# find_library(OPENSMT_RAW_LIB "opensmt2" PATHS "./lib" NO_DEFAULT_PATH )

# set(OPENSMT2_DIR "" CACHE PATH "Try to use particular OPENSMT2 install (set this to folder where OPEN_SMTConfig.cmake is installed)")
# find_package(OPENSMT2 REQUIRED)

find_library(OPENSMT2_DIR NAMES opensmt2 PATHS ${RAW_LIB_DIR} NO_DEFAULT_PATH)

message("Using OPENSMT2 library rooted at ${OPENSMT2_DIR}")
message("RAW_LIB_DIR ==> ${RAW_LIB_DIR}")

# # Get full path to OPENSMT2 executable
# get_target_property(OPENSMT2_FULL_PATH ${OPENSMT2_EXECUTABLE} LOCATION)
# message("Full path to OPENSMT2 binary is ${OPENSMT2_FULL_PATH}")

# JAVA package
set(CMAKE_SWIG_FLAGS -package org.sosy_lab.java_smt.solvers.opensmt2)
set(CMAKE_SWIG_OUTDIR "org/sosy_lab/java_smt/solvers/opensmt2")
# therefore
set(JAVA_API_DIR "build/org/sosy_lab/java_smt/solvers/opensmt2")

##################### END OF SET UP and VARIABLE SETTINGS ###############

# /JavaSMT/native-library-files/opensmt2/opensmt/src/api
# include_directories("../opensmt/src/api/") #here lies opensmt_c.h

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include/)

### USING SWIG: Build the C/C++ code into a library, accessed via our defined interface (in SWIG) 

# we are using C++
# set_property(SOURCE ${FOOBAR_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

#using swig : we generate a interface to interact with the earlier created library
swig_add_library(opensmt2Japi SHARED
			LANGUAGE Java
			SOURCES ${OPENSMT_SWIG_INTERFACE} 
					${CMAKE_CURRENT_SOURCE_DIR}/src/extOpemSMTSWIGapi.c
		)

# here we link the library and the api we  created for it together
# swig_link_libraries(opensmt2Japi PUBLIC ${OPENSMT_RAW_LIB})
swig_link_libraries(opensmt2Japi PUBLIC ${OPENSMT2_DIR})
# swig_link_libraries(opensmt2Japi PUBLIC opensmt2)


set_property(TARGET opensmt2Japi PROPERTY SWIG_COMPILE_OPTIONS -Wall -g)

target_include_directories(opensmt2Japi 
PRIVATE  ${CMAKE_CURRENT_SOURCE_DIR}/install_include/usr/local/include/opensmt/
PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include/
)

# message("CURRENT SRC DIR IS  ====>  ${CMAKE_CURRENT_SOURCE_DIR}")
# message("STP_INCLUDE_DIRS IS  ====>  ${STP_INCLUDE_DIRS}")

### END of Build the Shared Library API

# Build the library API now in JAVA - opensmt2JavaAPI.jar, linking the .so, and generated JNI java files
# For pyhton - swig_link_libraries(foobarPYapi foobarapi ${PYTHON_LIBRARIES} )
# For JAVA :

add_jar(
    opensmt2JavaAPI
    SOURCES    ${JAVA_API_DIR}/opensmt2Japi.java
			   ${JAVA_API_DIR}/opensmt2JapiJNI.java
			   ${JAVA_API_DIR}/osmt_context.java
)
add_dependencies( opensmt2JavaAPI opensmt2Japi )
