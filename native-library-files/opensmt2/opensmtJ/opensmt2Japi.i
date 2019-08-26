%module opensmt2Japi

%{
//#include "opensmt_c.h"
#include "extOpemSMTSWIGapi.h"
%}

//Possibly necessary extra includes
// %include "std_string.i"
//%include "enums.swg"
//%javaconst(1);
//%include "typemaps.i"

%nodefaultctor osmt_context;
struct osmt_context {};


//%include "opensmt_c.h"
%include extOpemSMTSWIGapi.h

