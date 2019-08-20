
# README: Scripts and Directory Structure

## ./stp

This contains STP source code, cloned from its Github repo. This folder is created by a script that clones the repo.

## ./stp_extend

In order to extend the STP api, it was necessary to directly modify some source files. This folder contains these source files : *c_interface.h*, *ext_c_interface.cpp* and *CMakeLists.txt*. These files should be modified directly in these folder since the build script will be copying them to replace the one in STP source. **Please edit the source for extending STP inside this folder**

## ./stpJ

Contains the folders and files necessary to build the Java Binding for STP. There is an attempt to extend the interface at the level of Java Binding the sources for this is in folders */stpJ/include/* and */stpJ/src/*.

The raw STP library (before binding) is installed inside the folder */stpJ/install_include/*, Cmake should locate it there. 

*/stpJ/build/* contains build files for the Java binding. The resulting object files are copied to their appropriate java-smt's library folders.

*/stpJ/StpJavaApi.i* is the SWIG interface used to generate an interface for the Java Binding.

## ./install_prereq.sh and ./dependencies

STP requires some dependencies, *./install_prereq.sh* calls a script inside *./dependencies/* which installs them. It also clones cryptominisat into this folder and build it before installing it.

## ./clean_up.sh

This removes build files for the binding and also the source files for cryptominisat.

## ./clean_and_build_stp.sh

This removes build files for the Java binding, then copies the STP extension files to replace corresponding files in the STP source. It then builds the raw STP.

## ./clean_clone_build_stp.sh

This removes all build files for raw STP and the Java binding. It also removes the STP source and reclones it for it Github repo. Then copies the STP extension files to replace corresponding files in the STP source. It then builds the raw STP.

## ./build_raw_to_java_api.sh

This is the script that builds the Java Binding for STP. It clones the STP source from Githib if not found otherwise it asks if you want to rebuild the raw STP, if 'y' it calls */clean_and_build_stp.sh* before going ahead to build the Java Binding.

