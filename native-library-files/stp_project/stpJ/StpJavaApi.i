%module StpJavaApi

//This is is where our API to STP is defined. We are basically customising
//the ../files/c_interface.h file in STP. The function names are unchanged.

%{ // Prepocessor code

// #ifndef _cvcl__include__c_interface_h_
// #define _cvcl__include__c_interface_h_
// #endif

#include <stdbool.h>

#include "extStpSWIGapi.h"

// struct StpEnv;
// typedef struct StpEnv StpEnv;
// typedef void* VC;
// typedef void* Expr;
// typedef void* Type;
// typedef void* WholeCounterExample;

int getNumOfAsserts(VC vc);

void addAssertFormula(VC vc, Expr e);
void push(VC vc);
void pop(VC vc);
int checkSAT_old(VC vc);
int checkSAT(VC vc, Expr e);

//adapted CPP Interface
StpEnv * createStpEnv(VC vc);
void destroyStpEnv(StpEnv * env);
int getCacheSize(StpEnv * env);
int getSymbolsSize(StpEnv * v);
void ext_push(StpEnv * env);
void ext_pop(StpEnv * env);
void ext_addFormula(StpEnv * env, Expr formula);
void ext_checkSat(StpEnv * env);

const char * getAllModel(VC vc);
%}

// Necessary extra includes
%include "typemaps.i"
%include "enums.swg"

%typemap(javain) enum SWIGTYPE "$javainput.ordinal()"
%typemap(javaout) enum SWIGTYPE {
    return $javaclassname.class.getEnumConstants()[$jnicall];
  }
%typemap(javabody) enum SWIGTYPE ""


/////////////////////////////////////////////////////////////////////////////
/// ENUMS
/////////////////////////////////////////////////////////////////////////////

// %include "enums.swg"
// %javaconst(1);

// Enum for Interface-only flags.
%inline %{
enum ifaceflag_t
{
  EXPRDELETE,
  MS,
  SMS,
  CMS4,
  RISS,
  MSP
};

//utility functions for this enum
void set_ifaceflag_t(enum ifaceflag_t h);
enum ifaceflag_t get_ifaceflag_t();
%}

// Enum that Covers all kinds of types that exist in STP.
%inline%{
enum type_t
{
  BOOLEAN_TYPE,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE
};

//utility functions for this enum
void set_type_t(enum type_t h);
enum type_t get_type_t();
%}

// Enum that Covers all kinds of expressions that exist in STP.
%inline%{
enum exprkind_t
{
  UNDEFINED, 
  SYMBOL,    
  BVCONST, 
  BVNOT,   
  BVCONCAT,
  BVOR,    
  BVAND,   
  BVXOR,   
  BVNAND, 
  BVNOR,  
  BVXNOR, 
  BVEXTRACT,
  BVLEFTSHIFT,
  BVRIGHTSHIFT,
  BVSRSHIFT,   
  BVPLUS,      
  BVSUB,       
  BVUMINUS,    
  BVMULT,      
  BVDIV,       
  BVMOD,       
  SBVDIV,      
  SBVREM,      
  SBVMOD,      
  BVSX,        
  BVZX,        
  ITE,         
  BOOLEXTRACT, 
  BVLT, 
  BVLE, 
  BVGT, 
  BVGE, 
  BVSLT,
  BVSLE,
  BVSGT,
  BVSGE,
  EQ,   
  FALSE,
  TRUE,
  NOT, 
  AND, 
  OR,  
  NAND,
  NOR, 
  XOR, 
  IFF, 
  IMPLIES,  
  PARAMBOOL,
  READ,     
  WRITE,    
  ARRAY,    
  BITVECTOR,
  BOOLEAN   
};

//utility functions for this enum
void set_exprkind_t(enum exprkind_t h);
enum exprkind_t get_exprkind_t();
%}

/////////////////////////////////////////////////////////////////////////////
/// CLASS TYPES
/////////////////////////////////////////////////////////////////////////////

// %{
// typedef void* VC;
// typedef void* Expr;
// typedef void* Type;
// typedef void* WholeCounterExample;
// %}

%nodefaultctor VC;
struct VC {};

%nodefaultctor Expr;
struct Expr {};

%nodefaultctor Type;
struct Type {};

%nodefaultctor WholeCounterExample;
struct WholeCounterExample {};

%nodefaultctor StpEnv;
struct StpEnv {};

/* 
%inline%{

// TODO: hanldle this in Java Code; Remove if confirmed. Envoronment configs
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

%}
 */

%inline%{

/////////////////////////////////////////////////////////////////////////////
/// EXTENTION ATTEMPTS
/////////////////////////////////////////////////////////////////////////////

int extraFunctionSum(int a, int b);

void extraSumUpto(int num);

void ext_AssertFormula(VC vc, Expr e);

int getNumOfAsserts(VC vc);

int getSomePrinting(VC vc);

char* getSomeXter(VC vc);

void addAssertFormula(VC vc, Expr e);
void push(VC vc);
void pop(VC vc);
int checkSAT_old(VC vc);

int checkSAT(VC vc, Expr e);

const char * getAllModel(VC vc);

//CPP
StpEnv * createStpEnv(VC vc);
void destroyStpEnv(StpEnv * env);
int getCacheSize(StpEnv * env);
int getSymbolsSize(StpEnv * v);
void ext_push(StpEnv * env);
void ext_pop(StpEnv * env);
void ext_addFormula(StpEnv * env, Expr formula);
void ext_checkSat(StpEnv * env);

/////////////////////////////////////////////////////////////////////////////
/// API INITIALISATION AND CONFIG
/////////////////////////////////////////////////////////////////////////////

const char* get_git_version_sha(void);

const char* get_git_version_tag(void);

const char* get_compilation_env(void);

void process_argument(const char ch, VC bm);

void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value);

VC vc_createValidityChecker(void);

Type vc_boolType(VC vc);

Type vc_arrayType(VC vc, Type typeIndex, Type typeData);

/////////////////////////////////////////////////////////////////////////////
/// EXPR MANUPULATION METHODS
/////////////////////////////////////////////////////////////////////////////

Expr vc_varExpr(VC vc, const char* name, Type type);

//Expr vc_varExpr1(VC vc, const char* name, int indexwidth,
//                            int valuewidth);

Type vc_getType(VC vc, Expr e);

int vc_getBVLength(VC vc, Expr e);

Expr vc_eqExpr(VC vc, Expr child0, Expr child1);

/////////////////////////////////////////////////////////////////////////////
/// BOOLEAN EXPRESSIONS
///
/// The following functions create boolean expressions.
/// The children provided as arguments must be of type boolean.
///
/// An exception is the function vc_iteExpr().
/// In the case of vc_iteExpr() the conditional must always be boolean,
/// but the thenExpr (resp. elseExpr) can be bit-vector or boolean type.
/// However, the thenExpr and elseExpr must be both of the same type.
///
/////////////////////////////////////////////////////////////////////////////

Expr vc_trueExpr(VC vc);

Expr vc_falseExpr(VC vc);

Expr vc_notExpr(VC vc, Expr child);

Expr vc_andExpr(VC vc, Expr left, Expr right);

Expr vc_andExprN(VC vc, Expr* children, int numOfChildNodes);

Expr vc_orExpr(VC vc, Expr left, Expr right);

Expr vc_orExprN(VC vc, Expr* children, int numOfChildNodes);

Expr vc_xorExpr(VC vc, Expr left, Expr right);

Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc);

Expr vc_iffExpr(VC vc, Expr left, Expr right);

Expr vc_iteExpr(VC vc, Expr conditional, Expr thenExpr, Expr elseExpr);

Expr vc_boolToBVExpr(VC vc, Expr form);

Expr vc_paramBoolExpr(VC vc, Expr var, Expr param);

/////////////////////////////////////////////////////////////////////////////
/// ARRAY EXPRESSIONS
/////////////////////////////////////////////////////////////////////////////

Expr vc_readExpr(VC vc, Expr array, Expr index);

Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue);

Expr vc_parseExpr(VC vc, const char* filepath);

void vc_printExpr(VC vc, Expr e);

void vc_printExprCCode(VC vc, Expr e);

char* vc_printSMTLIB(VC vc, Expr e);

void vc_printExprFile(VC vc, Expr e, int fd);

void vc_printStateToBuffer(VC vc, char **buf, unsigned long *len);

void vc_printExprToBuffer(VC vc, Expr e, char** buf,
                                     unsigned long* len);

void vc_printCounterExample(VC vc);

void vc_printVarDecls(VC vc);

void vc_clearDecls(VC vc);

// void vc_printAsserts(VC vc, int simplify_print _CVCL_DEFAULT_ARG(0));
void vc_printAsserts(VC vc, int simplify_print);


void vc_printQueryStateToBuffer(VC vc, Expr e, char** buf,
                                           unsigned long* len,
                                           int simplify_print);

void vc_printCounterExampleToBuffer(VC vc, char** buf, unsigned long* len);

void vc_printQuery(VC vc);

/////////////////////////////////////////////////////////////////////////////
/// CONTEXT RELATED METHODS
/////////////////////////////////////////////////////////////////////////////


void vc_assertFormula(VC vc, Expr e);

Expr vc_simplify(VC vc, Expr e);

int vc_query_with_timeout(VC vc, Expr e, int timeout_max_conflicts, int timeout_max_time);

int vc_query(VC vc, Expr e);

Expr vc_getCounterExample(VC vc, Expr e);

void vc_getCounterExampleArray(VC vc, Expr e, Expr** outIndices,
                                          Expr** outValues, int* outSize);

int vc_counterexample_size(VC vc);

void vc_push(VC vc);

void vc_pop(VC vc);

int getBVInt(Expr e);

unsigned int getBVUnsigned(Expr e);

unsigned long long int getBVUnsignedLongLong(Expr e);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR OPERATIONS
/////////////////////////////////////////////////////////////////////////////

Type vc_bvType(VC vc, int no_bits);

Type vc_bv32Type(VC vc);

//Const expressions for string, int, long-long, etc

Expr vc_bvConstExprFromDecStr(VC vc, int width,
                                         const char* decimalInput);

Expr vc_bvConstExprFromStr(VC vc, const char* binaryInput);

Expr vc_bvConstExprFromInt(VC vc, int bitWidth, unsigned int value);

Expr vc_bvConstExprFromLL(VC vc, int bitWidth,
                                     unsigned long long value);

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR ARITHMETIC OPERATIONS
/////////////////////////////////////////////////////////////////////////////

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right);

Expr vc_bvPlusExpr(VC vc, int bitWidth, Expr left, Expr right);

Expr vc_bvPlusExprN(VC vc, int bitWidth, Expr* children,
                               int numOfChildNodes);

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right);

Expr vc_bvMinusExpr(VC vc, int bitWidth, Expr left, Expr right);

Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right);

Expr vc_bvMultExpr(VC vc, int bitWidth, Expr left, Expr right);

Expr vc_bv32MultExpr(VC vc, Expr left, Expr right);

Expr vc_bvDivExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

Expr vc_bvModExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

Expr vc_sbvDivExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

Expr vc_sbvModExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

Expr vc_sbvRemExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR COMPARISON OPERATIONS
/////////////////////////////////////////////////////////////////////////////

Expr vc_bvLtExpr(VC vc, Expr left, Expr right);

Expr vc_bvLeExpr(VC vc, Expr left, Expr right);

Expr vc_bvGtExpr(VC vc, Expr left, Expr right);

Expr vc_bvGeExpr(VC vc, Expr left, Expr right);

Expr vc_sbvLtExpr(VC vc, Expr left, Expr right);

Expr vc_sbvLeExpr(VC vc, Expr left, Expr right);

Expr vc_sbvGtExpr(VC vc, Expr left, Expr right);

Expr vc_sbvGeExpr(VC vc, Expr left, Expr right);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR BITWISE OPERATIONS
/////////////////////////////////////////////////////////////////////////////

Expr vc_bvUMinusExpr(VC vc, Expr child);

Expr vc_bvAndExpr(VC vc, Expr left, Expr right);

Expr vc_bvOrExpr(VC vc, Expr left, Expr right);

Expr vc_bvXorExpr(VC vc, Expr left, Expr right);

Expr vc_bvNotExpr(VC vc, Expr child);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR SHIFT OPERATIONS
/////////////////////////////////////////////////////////////////////////////

Expr vc_bvLeftShiftExprExpr(VC vc, int bitWidth, Expr left,
                                       Expr right);

Expr vc_bvRightShiftExprExpr(VC vc, int bitWidth, Expr left,
                                        Expr right);

Expr vc_bvSignedRightShiftExprExpr(VC vc, int bitWidth, Expr left,
                                              Expr right);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR EXTRACTION & EXTENSION
/////////////////////////////////////////////////////////////////////////////

Expr vc_bvExtract(VC vc, Expr child, int high_bit_no,
                             int low_bit_no);

Expr vc_bvBoolExtract_Zero(VC vc, Expr x, int bit_no);

Expr vc_bvBoolExtract_One(VC vc, Expr x, int bit_no);

Expr vc_bvSignExtend(VC vc, Expr child, int newWidth);

/////////////////////////////////////////////////////////////////////////////
/// CONVENIENCE FUNCTIONS FOR ARRAYS
/////////////////////////////////////////////////////////////////////////////

/*C pointer support:  C interface to support C memory arrays in CVCL */

Expr vc_bvCreateMemoryArray(VC vc, const char* arrayName);

Expr vc_bvReadMemoryArray(VC vc, Expr array, Expr byteIndex,
                                     int numOfBytes);

Expr vc_bvWriteToMemoryArray(VC vc, Expr array, Expr byteIndex,
                                        Expr element, int numOfBytes);

/////////////////////////////////////////////////////////////////////////////
/// GENERAL EXPRESSION OPERATIONS
/////////////////////////////////////////////////////////////////////////////

char* exprString(Expr e);

char* typeString(Type t);

Expr getChild(Expr e, int n);

// This function is wrong 
//int vc_isBool(Expr e);

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg));


// ERROR HANDLER ToDo: Good but Error Handling here needs rework

//%callback("%(uppercase)s");
//void errorHandler(const char * err_msg)
//{
//    printf("Error: %s\n", err_msg);
//    exit(1);
//}
//%nocallback;


int vc_getHashQueryStateToBuffer(VC vc, Expr query);

void vc_Destroy(VC vc);

void vc_DeleteExpr(Expr e);

WholeCounterExample vc_getWholeCounterExample(VC vc);

Expr vc_getTermFromCounterExample(VC vc, Expr e, WholeCounterExample c);

void vc_deleteWholeCounterExample(WholeCounterExample cc);

enum exprkind_t getExprKind(Expr e);

int getDegree(Expr e);

int getBVLength(Expr e);

enum type_t getType(Expr e);

// get value bit width

int getVWidth(Expr e);

int getIWidth(Expr e);

void vc_printCounterExampleFile(VC vc, int fd);

const char* exprName(Expr e);

int getExprID(Expr ex);

int vc_parseMemExpr(VC vc, const char* s, Expr* outQuery,
                               Expr* outAsserts);

bool vc_supportsMinisat(VC vc);

bool vc_useMinisat(VC vc);

bool vc_isUsingMinisat(VC vc);

bool vc_supportsSimplifyingMinisat(VC vc);

bool vc_useSimplifyingMinisat(VC vc);

bool vc_supportsCryptominisat(VC vc);

bool vc_useCryptominisat(VC vc);

bool vc_isUsingCryptominisat(VC vc);

bool vc_supportsRiss(VC vc);

bool vc_useRiss(VC vc);

bool vc_isUsingRiss(VC vc);

%}