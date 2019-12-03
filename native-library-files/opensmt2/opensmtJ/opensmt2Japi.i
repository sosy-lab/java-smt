%module opensmt2Japi

%{

// #ifdef __cplusplus
// extern "C" {
// #endif
#include "extOpemSMTSWIGapi.h"

// #ifdef __cplusplus
// }
// #endif
// %}

//Possibly necessary extra includes
// %include "std_string.i"
//%include "enums.swg"
//%javaconst(1);
//%include "typemaps.i"

%nodefaultctor osmt_context;
struct osmt_context {};

%include extOpemSMTSWIGapi.h

