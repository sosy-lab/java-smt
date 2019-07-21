%module stpJapi

%{ // Prepocessor code

// // #include <stp/c_interface.h>
// // #include <stdio.h>
// // #include <stdlib.h>

%}

////////////////////////////

// Necessary extra includes
%include "typemaps.i"
%include "enums.swg"

%typemap(javain) enum SWIGTYPE "$javainput.ordinal()"
%typemap(javaout) enum SWIGTYPE {
    return $javaclassname.class.getEnumConstants()[$jnicall];
  }
%typemap(javabody) enum SWIGTYPE ""

// %inline %{
//   enum HairType { blonde, ginger, brunette };
//   void setHair(enum HairType h);
//   enum HairType getHair();
// %}


//////////////////////////////


//---- This results in Proper Java Enums ----//
// %include "enums.swg"
// %javaconst(1);

//! Enum for Interface-only flags.
//!
%inline %{
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

//utility functions
void set_ifaceflag_t(enum ifaceflag_t h);
enum ifaceflag_t get_ifaceflag_t();
%}

//! Enum that Covers all kinds of types that exist in STP.
//!
%inline%{
enum type_t
{
  BOOLEAN_TYPE,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE
};

//utility functions
void set_type_t(enum type_t h);
enum type_t get_type_t();
%}


//! Enum that Covers all kinds of expressions that exist in STP.
//!
%inline%{
enum exprkind_t
{
  UNDEFINED, //!< An undefined expression.
  SYMBOL,    //!< Named expression (or variable), i.e. created via 'vc_varExpr'.
  BVCONST, //!< Bitvector constant expression, i.e. created via 'vc_bvConstExprFromInt'.
  BVNOT,    //!< Bitvector bitwise-not
  BVCONCAT, //!< Bitvector concatenation
  BVOR,     //!< Bitvector bitwise-or
  BVAND,    //!< Bitvector bitwise-and
  BVXOR,    //!< Bitvector bitwise-xor
  BVNAND, //!< Bitvector bitwise not-and; OR nand (TODO: does this still exist?)
  BVNOR,  //!< Bitvector bitwise not-or; OR nor (TODO: does this still exist?)
  BVXNOR, //!< Bitvector bitwise not-xor; OR xnor (TODO: does this still exist?)
  BVEXTRACT,    //!< Bitvector extraction, i.e. via 'vc_bvExtract'.
  BVLEFTSHIFT,  //!< Bitvector left-shift
  BVRIGHTSHIFT, //!< Bitvector right-right
  BVSRSHIFT,    //!< Bitvector signed right-shift
  BVPLUS,       //!< Bitvector addition
  BVSUB,        //!< Bitvector subtraction
  BVUMINUS,     //!< Bitvector unary minus; OR negate expression
  BVMULT,       //!< Bitvector multiplication
  BVDIV,        //!< Bitvector division
  BVMOD,        //!< Bitvector modulo operation
  SBVDIV,       //!< Signed bitvector division
  SBVREM,       //!< Signed bitvector remainder
  SBVMOD,       //!< Signed bitvector modulo operation
  BVSX,         //!< Bitvector signed extend
  BVZX,         //!< Bitvector zero extend
  ITE,          //!< If-then-else
  BOOLEXTRACT,  //!< Bitvector boolean extraction
  BVLT,         //!< Bitvector less-than
  BVLE,         //!< Bitvector less-equals
  BVGT,         //!< Bitvector greater-than
  BVGE,         //!< Bitvector greater-equals
  BVSLT,        //!< Signed bitvector less-than
  BVSLE,        //!< Signed bitvector less-equals
  BVSGT,        //!< Signed bitvector greater-than
  BVSGE,        //!< Signed bitvector greater-equals
  EQ,           //!< Equality comparator
  FALSE,        //!< Constant false boolean expression
  TRUE,         //!< Constant true boolean expression
  NOT,          //!< Logical-not boolean expression
  AND,          //!< Logical-and boolean expression
  OR,           //!< Logical-or boolean expression
  NAND, //!< Logical-not-and boolean expression (TODO: Does this still exist?)
  NOR,  //!< Logical-not-or boolean expression (TODO: Does this still exist?)
  XOR,  //!< Logical-xor (either-or) boolean expression
  IFF,  //!< If-and-only-if boolean expression
  IMPLIES,   //!< Implication boolean expression
  PARAMBOOL, //!< Parameterized boolean expression
  READ,      //!< Array read expression
  WRITE,     //!< Array write expression
  ARRAY,     //!< Array creation expression
  BITVECTOR, //!< Bitvector creation expression
  BOOLEAN    //!< Boolean creation expression
};

//utility functions
void set_exprkind_t(enum exprkind_t h);
enum exprkind_t get_exprkind_t();
%}



//---- END of ENUMS ----//



//---------- TYPES ---------//

%{
typedef void* VC;
typedef void* Expr;
typedef void* Type;
typedef void* WholeCounterExample;
%}

%nodefaultctor VC;
struct VC {};

%nodefaultctor Expr;
struct Expr {};

%nodefaultctor Type;
struct Type {};

%nodefaultctor WholeCounterExample;
struct WholeCounterExample {};


%inline%{

// typedef void* VC;

//! \brief Processes the given flag represented as char for the given validity checker.
//!
//! The following flags are supported:
//!  - 'a': Disables optimization. TODO: What kind of optimization is meant here?
//!  - 'c': Enables construction of counter examples.
//!  - 'd': Enables construction and checking of counter examples. Superseeds flag 'c'.
//!  - 'm': Use SMTLib1 parser. Conflicts with using SMTLib2 parser.
//!  - 'n': Enables printing of the output. TODO: What is meant with output here?
//!  - 'p': Enables printing of counter examples.
//!  - 'q': Enables printing of array values in declared order.
//!  - 'r': Enables accermannisation.
//!  - 's': Sets the status flag to true. TODO: What consequenses does this have?
//!  - 't': Enables quick statistics. TODO: What is this?
//!  - 'v': Enables printing of nodes.
//!  - 'w': Enables word-level solving. TODO: What is mean with this?
//!  - 'y': Enables printing binaries. TODO: What is meant with this?
/*
 struct Flags {
	const char a;
	const char c;
	const char d;
	const char m;
	const char n;
	const char p;
	const char q;
	const char r;
	const char s;
	const char t;
	const char v;
	const char w;
	const char y;
} ProcessFlags ;= {
	.a = 'a',
	.c = 'c',
	.d = 'd',
	.m = 'm',
	.n = 'n',
	.p = 'p',
	.q = 'q',
	.r = 'r',
	.s = 's',
	.t = 't',
	.v = 'v',
	.w = 'w',
	.y = 'y'
};
 */

%}
//---------- END OF TYPES ---------//


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

void make_division_total(VC vc);

VC vc_createValidityChecker(void);

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