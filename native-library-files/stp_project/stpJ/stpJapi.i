%module stpJapi

%{ // Prepocessor code

#include <stp/c_interface.h>
// #include <stdio.h>
// #include <stdlib.h>
%}


//Possibly necessary extra includes

//%include "typemaps.i"

//---- This results in Proper Java Enums ----//
%include "enums.swg"
%javaconst(1);

//! Enum for Interface-only flags.
//!
enum ifaceflag_t
{
  //! Tells the validity checker that it is responsible for resource
  //! deallocation of its allocated expressions.
  //!
  //! This is set to true by default.
  //!
  //! Affected methods are:
  //!  - vc_arrayType
  //!  - vc_boolType
  //!  - vc_bvType
  //!  - vc_bv32Type
  //!  - vc_vcConstExprFromInt
  //!
  //! Changing this flag while STP is running may result in undefined behaviour.
  //!
  //! Use this with great care; otherwise memory leaks are very easily possible!
  //!
  EXPRDELETE,

  //! Use the minisat SAT solver.
  //!
  MS,

  //! Use a simplifying version of the minisat SAT solver.
  //!
  SMS,

  //! Use the crypto minisat version 4 or higher (currently version 5) solver.
  //!
  CMS4,

  //! Use the SAT solver Riss.
  //!
  RISS,

  //! \brief Deprecated: use `MS` instead!
  //!
  //! This used to be the array version of the minisat SAT solver.
  //!
  //! Currently simply forwards to MS.
  //!
  MSP

};

//---- END of ENUMS ----//
//DEAL WITH THE FOLLOWINF TYPES :
// typedef void* VC;
// typedef void* Expr;
// typedef void* Type;
// typedef void* WholeCounterExample;

/* Convert from Python --> C */
// %typemap(in) int {
//     $1 = PyInt_AsLong($input);
//}

/* Convert from C --> Python */
// %typemap(out) int {
//     $result = PyInt_FromLong($1);
// }


%inline%{

//! \brief Returns the C string for the git sha of STP
//!
const char* get_git_version_sha(void);

//! \brief Returns the C string for the git tag of STP
//!
const char* get_git_version_tag(void);

//! \brief Returns the C string for the compilation env of STP
//!
const char* get_compilation_env(void);

//!  - --- flag are in oroginal file
//!
//! This function panics if given an unsupported or unknown flag.
//!
void process_argument(const char ch, VC bm);

%}



///////////-------------OLD----------//////////////////////

// %include <stp/c_interface.h>

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

/*

%pragma(java) jniclassimports=%{
import foobar.*;
%}

%pragma(java) moduleimports=%{
import foobar.*;
%}


//%nspace foobar::FooBar

*/