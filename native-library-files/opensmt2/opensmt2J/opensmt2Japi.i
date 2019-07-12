%module opensmt2Japi

%{
#include "opensmt_c.h"
%}

//Possibly necessary extra includes
// %include "std_string.i"
%include "enums.swg"
%javaconst(1);
%include "typemaps.i"

%include "opensmt_c.h"

/*

%pragma(java) jniclassimports=%{
import foobar.*;
%}

%pragma(java) moduleimports=%{
import foobar.*;
%}


//%nspace foobar::FooBar

*/