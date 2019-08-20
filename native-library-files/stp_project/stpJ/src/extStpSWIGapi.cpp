#include "../include/extStpSWIGapi.h"

/*
    Normally c_interface.h should be extended here calling the cpp_interface.h
    However cpp_interface.h is not included in build files (STRANGE !!!)
    A Solution:
        Create ext_c_interface.cpp right inside STP and extend it there 
        then the extended functions can be part of the SWIG interface
 */

int getNumOfAsserts(VC vc)
{
  return 0;
}
