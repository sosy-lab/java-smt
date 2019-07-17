%module stpJapi

%{
#include <stp/c_interface.h>
#include <stdio.h>
#include <stdlib.h>
%}

//Possibly necessary extra includes
// %include "std_string.i"

%include "enums.swg"
%javaconst(1);
%include "typemaps.i"
/*
%typemap(javabase) 
				SWIGTYPE, SWIGTYPE *, 
				SWIGTYPE &, SWIGTYPE [], 
				SWIGTYPE (CLASS::*) "SWIG"

%typemap(javacode) SWIGTYPE, SWIGTYPE *, 
				   SWIGTYPE &, SWIGTYPE [], 
                   SWIGTYPE (CLASS::*) %{
			  protected long getPointer() {
			    return swigCPtr;
			  }
%}
*/
%include <stp/c_interface.h>


/*

%pragma(java) jniclassimports=%{
import foobar.*;
%}

%pragma(java) moduleimports=%{
import foobar.*;
%}


//%nspace foobar::FooBar

*/