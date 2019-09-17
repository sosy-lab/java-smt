

// #ifndef _cvcl__include__c_interface_h_
// #define _cvcl__include__c_interface_h_


#ifdef __cplusplus
#define _CVCL_DEFAULT_ARG(v) = v
#else
#define _CVCL_DEFAULT_ARG(v)
#endif

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>

// #include <stdbool.h>

// #include "stp/c_interface.h"

// #include <cassert>
// #include <cstdio>
// #include <cstdlib>

// #include "stp/Interface/fdstream.h"
// #include "stp/Parser/parser.h"
// #include "stp/Printer/printers.h"
// #include "stp/cpp_interface.h"
// #include "stp/Util/GitSHA1.h"
// FIXME: External library
// #include "extlib-abc/cnf_short.h"

// using std::cout;
// using std::ostream;
// using std::stringstream;
// using std::string;
// using std::fdostream;
// using std::endl;

// typedef void* VC;
// typedef void* Expr;
// typedef void* Type;
// typedef void* WholeCounterExample;

//CPP
struct StpEnv;
typedef struct StpEnv StpEnv;
typedef void* VC;
typedef void* Expr;
typedef void* Type;
typedef void* WholeCounterExample;

int getNumOfAsserts(VC vc);

#ifdef __cplusplus
}
#endif

// #undef DLL_PUBLIC // Undefine internal macro to prevent it from leaking into the API.
// #undef DLL_LOCAL // Undefine internal macro to prevent it from leaking into the API.

#undef _CVCL_DEFAULT_ARG // Undefine macro to not pollute global macro namespace!

// #endif // _cvcl__include__c_interface_h_

