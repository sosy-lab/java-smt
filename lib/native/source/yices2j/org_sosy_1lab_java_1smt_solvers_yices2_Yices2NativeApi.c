#include<stdint.h>

#include "includes/defines.h"

/*
 * Copied from the Sun JNI Programmer's Guide and Specification
 */
void throwException(JNIEnv *env, const char *name, const char *msg) {
	jclass cls = (*env)->FindClass(env, name);
	if (cls != NULL) {
		(*env)->ThrowNew(env, cls, msg);
	}
}

/*
 * Functions for initializing and freeing Yices internal data structures.
 * Call init() before doing anything else to initialize data structures.
 * Call exit() after to free allocated memory
 */
DEFINE_FUNC(void, 1init) WITHOUT_ARGS
VOID_CALL0(init)

DEFINE_FUNC(void, 1exit) WITHOUT_ARGS
VOID_CALL0(exit)

DEFINE_FUNC(void, 1reset) WITHOUT_ARGS
VOID_CALL0(reset)

DEFINE_FUNC(void, 1free_1string) WITH_ONE_ARG(long)
POINTER_ARG(char, 1)
VOID_CALL1(free_string)


/*
 * Create new Yices cnfiguration.
 */
DEFINE_FUNC(jconf, 1new_1config) WITHOUT_ARGS
CALL0(ctx_config_t *, new_config)
CONF_RETURN

/*
 * Delete the specified Yices configuration.
 */
DEFINE_FUNC(void, 1free_1config) WITH_ONE_ARG(jconf)
CONF_ARG_VOID(1)
VOID_CALL1(free_config)

/*
 * Set Yices configuration option.
 */

DEFINE_FUNC(int, 1set_1config) WITH_THREE_ARGS(jconf, string, string)
CONF_ARG(1)
STRING_ARG(2)
STRING_ARG(3)
CALL3(int, set_config)
FREE_STRING_ARG(2)
FREE_STRING_ARG(3)
INT_RETURN

DEFINE_FUNC(int, 1default_1config_1for_1logic) WITH_TWO_ARGS(jconf, string)
CONF_ARG(1)
STRING_ARG(2)
CALL2(int, default_config_for_logic)
FREE_STRING_ARG(2)
INT_RETURN

/*
 * Create Yices context with specified configuration.
 */
DEFINE_FUNC(jctx, 1new_1context) WITH_ONE_ARG(jconf)
CONF_ARG(1)
//ctx_config_t * m_arg1 = (ctx_config_t *) arg1;
CALL1(context_t *, new_context)
CTX_RETURN
//return (long) retval;
//}

/*
 * Delete specified Yices context.
 */
DEFINE_FUNC(void, 1free_1context) WITH_ONE_ARG(jctx)
CTX_ARG_VOID(1)
//context_t * m_arg1 = (context_t *) arg1;
VOID_CALL1(free_context)

/*
 *Preprocessing options
 */

DEFINE_FUNC(int, 1context_1enable_1option) WITH_TWO_ARGS(jctx, string)
CTX_ARG(1)
STRING_ARG(2)
CALL2(int, context_enable_option)
FREE_STRING_ARG(2)
INT_RETURN

DEFINE_FUNC(int, 1context_1disable_1option) WITH_TWO_ARGS(jctx, string)
CTX_ARG(1)
STRING_ARG(2)
CALL2(int, context_disable_option)
FREE_STRING_ARG(2)
INT_RETURN

/*
 *Search parameters
 */

DEFINE_FUNC(long, 1new_1param_1record) WITHOUT_ARGS
CALL0(param_t*, new_param_record)
PARAM_RETURN

DEFINE_FUNC(int, 1set_1param) WITH_THREE_ARGS(jparam, string, string)
PARAM_ARG(1)
STRING_ARG(2)
STRING_ARG(3)
CALL3(int, set_param)
FREE_STRING_ARG(2)
FREE_STRING_ARG(3)
INT_RETURN

DEFINE_FUNC(void, 1default_1params_1for_1context) WITH_TWO_ARGS(jctx, jparam)
CTX_ARG(1)
PARAM_ARG(2)
VOID_CALL2(default_params_for_context)

DEFINE_FUNC(void, 1free_1param_1record) WITH_ONE_ARG(jparam)
PARAM_ARG(1)
VOID_CALL1(free_param_record)

/*
 * Yices type constructors
 */

DEFINE_FUNC(jtype, 1bool_1type) WITHOUT_ARGS
CALL0(type_t, bool_type)
TYPE_RETURN

DEFINE_FUNC(jtype, 1int_1type) WITHOUT_ARGS
CALL0(type_t, int_type)
TYPE_RETURN

DEFINE_FUNC(jtype, 1real_1type) WITHOUT_ARGS
CALL0(type_t, real_type)
TYPE_RETURN

DEFINE_FUNC(jtype, 1bv_1type) WITH_ONE_ARG (int)
UINT32_ARG(1)
CALL1(type_t, bv_type)
TYPE_RETURN

//scalar type skipped

// uninterpreted type skipped

// tuple types skipped

//Might not work because of array handling
DEFINE_FUNC(jtype, 1function_1type) WITH_THREE_ARGS(int, jtypeArray, jtype)
UINT32_ARG(1)
TYPE_ARRAY_ARG(2)
TYPE_ARG(3)
CALL3(type_t, function_type)
FREE_TYPE_ARRAY_ARG(2)
TYPE_RETURN
//might not work

//redundant function types skipped

/*
 * Yices type tests
 */

yices_type_is(bool)

yices_type_is(int)

yices_type_is(real)

//check if type is arithmetic (int or real)
yices_type_is(arithmetic)

yices_type_is(bitvector)

//tests for previously skipped types skipped

yices_type_is(function)

//checks if type1 is subtype of type 2
DEFINE_FUNC(jboolean, 1type_1test_1subtype) WITH_TWO_ARGS(jtype, jtype)
TYPE_ARG(1)
TYPE_ARG(2)
CALL2(int, test_subtype)
BOOLEAN_RETURN

//checks if type 1 and type2 are compatible
DEFINE_FUNC(jboolean, 1compatible_1types) WITH_TWO_ARGS(jtype, jtype)
TYPE_ARG(1)
TYPE_ARG(2)
CALL2(int, compatible_types)
BOOLEAN_RETURN

//todo add missing type properties
// certain type properies return -1 for error, 0 for success needs checking

DEFINE_FUNC(int, 1bvtype_1size) WITH_ONE_ARG(jtype)
TYPE_ARG(1)
CALL1(int, bvtype_size)
INT_RETURN

//skipping scalar_type_card()

DEFINE_FUNC(int, 1type_1num_1children) WITH_ONE_ARG(jtype)
TYPE_ARG(1)
CALL1(int, type_num_children)
INT_RETURN

DEFINE_FUNC(jtype, 1type_1child) WITH_TWO_ARGS(jtype, int)
TYPE_ARG(1)
SIMPLE_ARG(int32_t, 2)
CALL2(type_t, type_child)
TYPE_RETURN

DEFINE_FUNC(intArray, 1type_1children) WITH_ONE_ARG(jtype)
TYPE_ARG(1)
TYPE_VECTOR_ARG(2)
CALL2(int, type_children)
TYPE_VECTOR_ARG_RETURN(2)

/*
 * Term construction
 */

DEFINE_FUNC(jterm, 1new_1uninterpreted_1term) WITH_ONE_ARG(jtype)
TYPE_ARG(1)
CALL1(term_t, new_uninterpreted_term)
TERM_RETURN

DEFINE_FUNC(jterm, 1new_1variable) WITH_ONE_ARG(jtype)
TYPE_ARG(1)
CALL1(term_t, new_variable)
TERM_RETURN

DEFINE_FUNC(jterm, 1constant) WITH_TWO_ARGS(jtype, int)
TYPE_ARG(1)
SIMPLE_ARG(int32_t, 2)
CALL2(term_t, constant)
TERM_RETURN

DEFINE_FUNC(jterm, 1ite) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, ite)
TERM_RETURN

DEFINE_FUNC(jterm, 1eq) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, eq)
TERM_RETURN

DEFINE_FUNC(jterm, 1neq) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, neq)
TERM_RETURN

DEFINE_FUNC(jterm, 1distinct) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, distinct)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1application) WITH_THREE_ARGS(jterm, int, jtermArray)
TERM_ARG(1)
UINT32_ARG(2)
TERM_ARRAY_ARG(3)
CALL3(term_t, application)
FREE_TERM_ARRAY_ARG(3)
TERM_RETURN

//skipping redundant functions

//skipping tuple fuctions

DEFINE_FUNC(jterm, 1update) WITH_FOUR_ARGS(jterm, int, jtermArray, jterm)
TERM_ARG(1)
UINT32_ARG(2)
TERM_ARRAY_ARG(3)
TERM_ARG(4)
CALL4(term_t, update)
FREE_TERM_ARRAY_ARG(3)
TERM_RETURN

//skipping redundant functions

DEFINE_FUNC(jterm, 1forall) WITH_THREE_ARGS(int, jtermArray, jterm)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
TERM_ARG(3)
CALL3(term_t, forall)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1exists) WITH_THREE_ARGS(int, jtermArray, jterm)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
TERM_ARG(3)
CALL3(term_t, exists)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1lambda) WITH_THREE_ARGS(int, jtermArray, jterm)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
TERM_ARG(3)
CALL3(term_t, lambda)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

/*
 * Boolean terms
 */

DEFINE_FUNC(jterm, 1true) WITHOUT_ARGS
CALL0(term_t, true)
TERM_RETURN

DEFINE_FUNC(jterm, 1false) WITHOUT_ARGS
CALL0(term_t, false)
TERM_RETURN

DEFINE_FUNC(jterm, 1not) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, not)
TERM_RETURN

DEFINE_FUNC(jterm, 1and) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, and)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1and2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, and2)
TERM_RETURN

DEFINE_FUNC(jterm, 1and3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, and3)
TERM_RETURN

DEFINE_FUNC(jterm, 1or) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, or)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1or2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, or2)
TERM_RETURN

DEFINE_FUNC(jterm, 1or3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, or3)
TERM_RETURN

DEFINE_FUNC(jterm, 1xor) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, xor)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1xor2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, xor2)
TERM_RETURN

DEFINE_FUNC(jterm, 1xor3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, xor3)
TERM_RETURN

DEFINE_FUNC(jterm, 1iff) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, iff)
TERM_RETURN

DEFINE_FUNC(jterm, 1implies) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, implies)
TERM_RETURN

/*
 * ARITHMETIC TERMS
 */

DEFINE_FUNC(jterm, 1zero) WITHOUT_ARGS
CALL0(term_t, zero)
TERM_RETURN

DEFINE_FUNC(jterm, 1int32) WITH_ONE_ARG(int)
SIMPLE_ARG(int32_t, 1)
CALL1(term_t, int32)
TERM_RETURN

DEFINE_FUNC(jterm, 1int64) WITH_ONE_ARG(long)
SIMPLE_ARG(int64_t, 1)
CALL1(term_t, int64)
TERM_RETURN

DEFINE_FUNC(jterm, 1rational32) WITH_TWO_ARGS(int, int)
SIMPLE_ARG(int32_t, 1)
UINT32_ARG(2)
CALL2(term_t, rational32)
TERM_RETURN

DEFINE_FUNC(jterm, 1rational64) WITH_TWO_ARGS(long, long)
SIMPLE_ARG(int64_t, 1)
SIMPLE_ARG(uint64_t, 2)
CALL2(term_t, rational64)
TERM_RETURN

//skipping GMP functions

DEFINE_FUNC(jterm, 1parse_1rational) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, parse_rational)
FREE_STRING_ARG(1)
TERM_RETURN

DEFINE_FUNC(jterm, 1parse_1float) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, parse_float)
FREE_STRING_ARG(1)
TERM_RETURN

DEFINE_FUNC(jterm, 1add) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, add)
TERM_RETURN

DEFINE_FUNC(jterm, 1sub) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, sub)
TERM_RETURN

DEFINE_FUNC(jterm, 1neg) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, neg)
TERM_RETURN

DEFINE_FUNC(jterm, 1mul) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, mul)
TERM_RETURN

DEFINE_FUNC(jterm, 1square) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, square)
TERM_RETURN

DEFINE_FUNC(jterm, 1power) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, power)
TERM_RETURN

DEFINE_FUNC(jterm, 1division) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, division)
TERM_RETURN

DEFINE_FUNC(jterm, 1sum) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, sum)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1product) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, product)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1poly_1int32) WITH_THREE_ARGS(int, intArray, jtermArray)
UINT32_ARG(1)
INT_ARRAY_ARG(int32_t, 2)
TERM_ARRAY_ARG(3)
CALL3(term_t, poly_int32)
FREE_INT_ARRAY_ARG(2)
FREE_TERM_ARRAY_ARG(3)
TERM_RETURN

DEFINE_FUNC(jterm, 1poly_1int64) WITH_THREE_ARGS(int, longArray, jtermArray)
UINT32_ARG(1)
LONG_ARRAY_ARG(int64_t, 2)
TERM_ARRAY_ARG(3)
CALL3(term_t, poly_int64)
FREE_LONG_ARRAY_ARG(2)
FREE_TERM_ARRAY_ARG(3)
TERM_RETURN

DEFINE_FUNC(jterm, 1poly_1rational32) WITH_FOUR_ARGS(int, intArray, intArray, jtermArray)
UINT32_ARG(1)
INT_ARRAY_ARG(int32_t, 2)
INT_ARRAY_ARG(uint32_t, 3)
TERM_ARRAY_ARG(4)
CALL4(term_t, poly_rational32)
FREE_INT_ARRAY_ARG(2)
FREE_INT_ARRAY_ARG(3)
FREE_TERM_ARRAY_ARG(4)
TERM_RETURN

DEFINE_FUNC(jterm, 1poly_1rational64) WITH_FOUR_ARGS(int, longArray, longArray, jtermArray)
UINT32_ARG(1)
LONG_ARRAY_ARG(int64_t, 2)
LONG_ARRAY_ARG(uint64_t, 3)
TERM_ARRAY_ARG(4)
CALL4(term_t, poly_rational64)
FREE_LONG_ARRAY_ARG(2)
FREE_LONG_ARRAY_ARG(3)
FREE_TERM_ARRAY_ARG(4)
TERM_RETURN

//skipping gmp functions

DEFINE_FUNC(jterm, 1abs) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, abs)
TERM_RETURN

DEFINE_FUNC(jterm, 1floor) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, floor)
TERM_RETURN

DEFINE_FUNC(jterm, 1ceil) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, ceil)
TERM_RETURN

DEFINE_FUNC(jterm, 1idiv) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, idiv)
TERM_RETURN

DEFINE_FUNC(jterm, 1imod) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, imod)
TERM_RETURN

/*
 * Arith operations with two arguments
 */
yices_arith2(eq)//, atom)
yices_arith2(neq)//, atom)
yices_arith2(geq)//, atom)
yices_arith2(leq)//, atom)
yices_arith2(gt)//, atom)
yices_arith2(lt)//, atom)

/*
 * Arith operations with one argument
 */
yices_arith(eq0) //_atom)
yices_arith(neq0) //_atom)
yices_arith(geq0) //_atom)
yices_arith(leq0) //_atom)
yices_arith(gt0) //_atom)
yices_arith(lt0) //_atom)

DEFINE_FUNC(jterm, 1divides_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, divides_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1is_1int_1atom) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, is_int_atom)
TERM_RETURN

/*
 * BITVECTOR TERMS
 */

DEFINE_FUNC(jterm, 1bvconst_1uint32) WITH_TWO_ARGS(int, int)
UINT32_ARG(1)
UINT32_ARG(2)
CALL2(term_t, bvconst_uint32)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconst_1uint64) WITH_TWO_ARGS(int, long)
UINT32_ARG(1)
SIMPLE_ARG(uint64_t, 2)
CALL2(term_t, bvconst_uint64)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconst_1int32) WITH_TWO_ARGS (int, int)
UINT32_ARG(1)
SIMPLE_ARG(int32_t, 2)
CALL2(term_t, bvconst_int32)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconst_1int64) WITH_TWO_ARGS(int, long)
UINT32_ARG(1)
SIMPLE_ARG(int64_t, 2)
CALL2(term_t, bvconst_int64)
TERM_RETURN

//GMP FUnctions skipped

DEFINE_FUNC(jterm, 1bvconst_1zero) WITH_ONE_ARG(int)
UINT32_ARG(1)
CALL1(term_t, bvconst_zero)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconst_1one) WITH_ONE_ARG(int)
UINT32_ARG(1)
CALL1(term_t, bvconst_one)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconst_1minus_1one) WITH_ONE_ARG(int)
UINT32_ARG(1)
CALL1(term_t, bvconst_minus_one)
TERM_RETURN

//int32_t > Integer_MAX_VALUE?
DEFINE_FUNC(jterm, 1bvconst_1from_1array) WITH_TWO_ARGS(int, intArray)
UINT32_ARG(1)
INT_ARRAY_ARG(int32_t, 2)
CALL2(term_t, bvconst_from_array)
FREE_INT_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1parse_1bvbin) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, parse_bvbin)
FREE_STRING_ARG(1)
TERM_RETURN

DEFINE_FUNC(jterm, 1parse_1bvhex) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, parse_bvhex)
FREE_STRING_ARG(1)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvadd) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvadd)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsub) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsub)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvneg) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, bvneg)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvmul) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvmul)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsquare) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, bvsquare)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvpower) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, bvpower)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsum) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvsum)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvproduct) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvproduct)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvdiv) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvdiv)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvrem) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvrem)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsdiv) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsdiv)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsrem) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsrem)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsmod) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsmod)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvnot) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, bvnot)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvand) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvand)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvand2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvand2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvand3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, bvand3)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvor) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvor)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvor2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvor2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvor3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, bvor3)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvxor) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvxor)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvxor2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvxor2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvxor3) WITH_THREE_ARGS(jterm, jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
TERM_ARG(3)
CALL3(term_t, bvxor3)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvnand) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvnand)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvnor) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvnor)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvxnor) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvxnor)
TERM_RETURN

DEFINE_FUNC(jterm, 1shift_1left0) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, shift_left0)
TERM_RETURN

DEFINE_FUNC(jterm, 1shift_1left1) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, shift_left1)
TERM_RETURN

DEFINE_FUNC(jterm, 1shift_1right0) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, shift_right0)
TERM_RETURN

DEFINE_FUNC(jterm, 1shift_1right1) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, shift_right1)
TERM_RETURN

DEFINE_FUNC(jterm, 1ashift_1right) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, ashift_right)
TERM_RETURN

DEFINE_FUNC(jterm, 1rotate_1left) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, rotate_left)
TERM_RETURN

DEFINE_FUNC(jterm, 1rotate_1right) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, rotate_right)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvshl) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvshl)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvlshr) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvlshr)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvashr) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvashr)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvextract) WITH_THREE_ARGS(jterm, int, int)
TERM_ARG(1)
UINT32_ARG(2)
UINT32_ARG(3)
CALL3(term_t, bvextract)
TERM_RETURN

DEFINE_FUNC(jterm, 1bitextract) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, bitextract)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconcat) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvconcat)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvconcat2) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvconcat2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvrepeat) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, bvrepeat)
TERM_RETURN

DEFINE_FUNC(jterm, 1sign_1extend) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, sign_extend)
TERM_RETURN

DEFINE_FUNC(jterm, 1zero_1extend) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
UINT32_ARG(2)
CALL2(term_t, zero_extend)
TERM_RETURN

DEFINE_FUNC(jterm, 1redand) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, redand)
TERM_RETURN

DEFINE_FUNC(jterm, 1redor) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, redor)
TERM_RETURN

DEFINE_FUNC(jterm, 1redcomp) WITH_TWO_ARGS(jterm,jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, redcomp)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvarray) WITH_TWO_ARGS(int, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
CALL2(term_t, bvarray)
FREE_TERM_ARRAY_ARG(2)
TERM_RETURN

DEFINE_FUNC(jterm, 1bveq_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bveq_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvneq_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvneq_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvge_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvge_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvgt_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvgt_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvle_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvle_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvlt_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvlt_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsge_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsge_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsgt_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsgt_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvsle_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvsle_atom)
TERM_RETURN

DEFINE_FUNC(jterm, 1bvslt_1atom) WITH_TWO_ARGS(jterm, jterm)
TERM_ARG(1)
TERM_ARG(2)
CALL2(term_t, bvslt_atom)
TERM_RETURN

/*
 * TERM PROPERTIES
 */

DEFINE_FUNC(jtype, 1type_1of_1term) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(type_t, type_of_term)
TYPE_RETURN

//SEPERATE ERROR HANDLING NEEDED? 0 is false and error
yices_term_is(bool)

yices_term_is(int)

yices_term_is(real)

yices_term_is(arithmetic)

yices_term_is(bitvector)

//scalar + tuple skipped

yices_term_is(function)

DEFINE_FUNC(int, 1term_1bitsize) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(int, term_bitsize)
INT_RETURN

//SEPERATE ERROR HANDLING NEEDED? 0 is false and error
DEFINE_FUNC(jboolean, 1term_1is_1ground) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(int, term_is_ground)
BOOLEAN_RETURN

//SEPERATE ERROR HANDLING NEEDED? 0 is false and error
yices_term_is(atomic)

yices_term_is(composite)

yices_term_is(projection)

yices_term_is(sum)

yices_term_is(bvsum)

yices_term_is(product)

//Handle naming in Java/ returns -1 if YICES_CONSTRUCTOR_ERROR
DEFINE_FUNC(int, 1term_1constructor) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_constructor_t, term_constructor)
INT_RETURN

//returns -1 if term not valid
DEFINE_FUNC(int, 1term_1num_1children) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(int, term_num_children)
INT_RETURN

DEFINE_FUNC(jterm, 1term_1child) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
SIMPLE_ARG(int32_t, 2)
CALL2(term_t, term_child)
TERM_RETURN

//Maybe not needed
DEFINE_FUNC(int, 1proj_1index) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(int, proj_index)
INT_RETURN

//Maybe not needed
DEFINE_FUNC(jterm, 1proj_1arg) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(term_t, proj_arg)
TERM_RETURN

DEFINE_FUNC(int, 1bool_1const_1value) WITH_ONE_ARG(jterm)
TERM_ARG(1)
INT_POINTER_ARG(2)
CALL2(int, bool_const_value)
FROM_INT_POINTER_RETURN(2)

DEFINE_FUNC(intArray, 1bv_1const_1value) WITH_TWO_ARGS(jterm, int)
TERM_ARG(1)
EMPTY_INT_ARRAY_ARG(int32_t, 2)
CALL2(int, bv_const_value)
INT_ARRAY_RETURN(2)

DEFINE_FUNC(string, 1rational_1const_1value) WITH_ONE_ARG(jterm)
TERM_ARG(1)
MPQ_ARG(2)
CALL2(int, rational_const_value)
MPQ_RETURN(2)

//skipping scalar const value | rational const value | sum component
//skipping bvsum component because it has two returns
//skipping product_component because it has two returns


//Skipping functions from yices_bool_const_value as need is unclear
//todo add missing type properties
// certain return -1 for error, 0 for success needs checking

/*
 * Assertions and SAT Checking
 */

DEFINE_FUNC(int, 1context_1status) WITH_ONE_ARG(jctx)
CTX_ARG(1)
CALL1(smt_status_t, context_status)
INT_RETURN

DEFINE_FUNC(int, 1assert_1formula) WITH_TWO_ARGS(jctx, jterm)
CTX_ARG(1)
TERM_ARG(2)
CALL2(int, assert_formula)
INT_RETURN

DEFINE_FUNC(int, 1assert_1formulas) WITH_THREE_ARGS(jctx, int, jtermArray)
CTX_ARG(1)
UINT32_ARG(2)
TERM_ARRAY_ARG(3)
CALL3(int, assert_formulas)
FREE_TERM_ARRAY_ARG(3)
INT_RETURN

//todo parameter handling
DEFINE_FUNC(int, 1check_1context) WITH_TWO_ARGS (jctx, jparam)
CTX_ARG(1)
PARAM_ARG(2)
CALL2(smt_status_t, check_context)
INT_RETURN

DEFINE_FUNC(void, 1stop_1search) WITH_ONE_ARG(jctx)
CTX_ARG(1)
VOID_CALL1(stop_search)

DEFINE_FUNC(void, 1reset_1context) WITH_ONE_ARG(jctx)
CTX_ARG(1)
VOID_CALL1(reset_context)

DEFINE_FUNC(int, 1assert_1blocking_1clause) WITH_ONE_ARG(jctx)
CTX_ARG(1)
CALL1(int, assert_blocking_clause)
INT_RETURN

DEFINE_FUNC(int, 1push) WITH_ONE_ARG(jctx)
CTX_ARG(1)
CALL1(int, push)
INT_RETURN

DEFINE_FUNC(int, 1pop) WITH_ONE_ARG(jctx)
CTX_ARG(1)
CALL1(int, pop)
INT_RETURN

DEFINE_FUNC(int, 1check_1context_1with_1assumptions) WITH_FOUR_ARGS (jctx, jparam, int, jtermArray)
CTX_ARG(1)
PARAM_ARG(2)
UINT32_ARG(3)
TERM_ARRAY_ARG(4)
CALL4(smt_status_t, check_context_with_assumptions)
FREE_TERM_ARRAY_ARG(4)
INT_RETURN

//untested
DEFINE_FUNC(jtermArray, 1get_1unsat_1core) WITH_ONE_ARG(jctx)
CTX_ARG(1)
TERM_VECTOR_ARG(2)
CALL2(int, get_unsat_core)
TERM_VECTOR_ARG_RETURN(2)

/*
 * Model Generation and Exploration
 */

DEFINE_FUNC(jmodel, 1get_1model) WITH_TWO_ARGS(jctx, int)
CTX_ARG(1)
SIMPLE_ARG(int32_t, 2)
CALL2(model_t *, get_model)
MODEL_RETURN

DEFINE_FUNC(jmodel, 1model_1from_1map) WITH_THREE_ARGS(int ,jtermArray, jtermArray)
UINT32_ARG(1)
TERM_ARRAY_ARG(2)
TERM_ARRAY_ARG(3)
CALL3(model_t *, model_from_map)
FREE_TERM_ARRAY_ARG(2)
FREE_TERM_ARRAY_ARG(3)
MODEL_RETURN

//1model_1collect_1defined_1terms

DEFINE_FUNC(jtermArray, 1def_1terms) WITH_ONE_ARG(jmodel)
MODEL_ARG(1)
TERM_VECTOR_ARG(2)
VOID_CALL2_WITH_RETURN(model_collect_defined_terms)
int retval = 0; //declare retval for TERM_VECTOR_ARG_RETURN
TERM_VECTOR_ARG_RETURN(2)

//yices_exit includes free_model()
DEFINE_FUNC(void, 1free_1model) WITH_ONE_ARG(jmodel)
MODEL_ARG(1)
VOID_CALL1(free_model)

/*
 * TERM VALUES IN MODEL
 */

DEFINE_FUNC(int, 1get_1bool_1value) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
INT_POINTER_ARG(3)
CALL3(int, get_bool_value)
FROM_INT_POINTER_RETURN(3)

DEFINE_FUNC(int, 1get_1int32_1value) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
INT_POINTER_ARG(3)
CALL3(int, get_bool_value)
FROM_INT_POINTER_RETURN(3)

DEFINE_FUNC(long, 1get_1int64_1value) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
LONG_POINTER_ARG(3)
CALL3(int, get_int64_value)
FROM_LONG_POINTER_RETURN(3)

// skipping get_rational32 | get_rational_64 TWO RETURN_VALUES

DEFINE_FUNC(double, 1get_1_double_value) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
DOUBLE_POINTER_ARG(3)
CALL3(int, get_double_value)
FROM_DOUBLE_POINTER_RETURN(3)

//skipping gmp functions

//skipping get_algebraic_number_value

DEFINE_FUNC(intArray, 1get_1bv_1value) WITH_THREE_ARGS(jmodel, jterm, int)
MODEL_ARG(1)
TERM_ARG(2)
EMPTY_INT_ARRAY_ARG(int32_t, 3)
CALL3(int, get_bv_value)
INT_ARRAY_RETURN(3)

//skipping get_scalar_value
//use boolean as return?

DEFINE_FUNC(int, 1formula_1true_1in_1model) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
CALL2(int, formula_true_in_model)
INT_RETURN
//use boolean as return?
DEFINE_FUNC(int, 1formulas_1true_1in_1model) WITH_THREE_ARGS(jmodel, int, jtermArray)
MODEL_ARG(1)
UINT32_ARG(2)
TERM_ARRAY_ARG(3)
CALL3(int, formulas_true_in_model)
FREE_TERM_ARRAY_ARG(3)
INT_RETURN

DEFINE_FUNC(intArray, 1get_1value) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
EMPTY_YVAL_ARG(3)
CALL3(int, get_value)
YVAL_RETURN(3)

DEFINE_FUNC(int, 1val_1bitsize) WITH_THREE_ARGS(jmodel, jnodeid, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2, 2, 3)
CALL2(int, val_bitsize)
INT_RETURN

DEFINE_FUNC(int, 1val_1function_1arity) WITH_THREE_ARGS(jmodel, jnodeid, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2, 2, 3)
CALL2(int, val_function_arity)
INT_RETURN

DEFINE_FUNC(int, 1val_1get_1bool) WITH_THREE_ARGS(jmodel, jnodeid, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2, 2, 3)
INT_POINTER_ARG(3)
CALL3(int, val_get_bool)
FROM_INT_POINTER_RETURN(3)

DEFINE_FUNC(string, 1val_1get_1mpq) WITH_THREE_ARGS(jmodel, jnodeid, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2, 2, 3)
MPQ_ARG(3)
CALL3(int, val_get_mpq)
MPQ_RETURN(3)


DEFINE_FUNC(intArray, 1val_1get_1bv) WITH_FOUR_ARGS(jmodel, jnodeid, int, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2, 2, 4)
EMPTY_INT_ARRAY_ARG(int32_t, 3)
CALL3(int, val_get_bv)
INT_ARRAY_RETURN(3)

DEFINE_FUNC(intArray, 1val_1expand_1function) WITH_THREE_ARGS(jmodel, jnodeid, jnodetag)
MODEL_ARG(1)
YVAL_ARG(2,2,3)
EMPTY_YVAL_ARG(3)
YVAL_VECTOR_ARG(4)
CALL4(int, val_expand_function)
jintArray jretval = NULL;
if(retval == -1){  
  const char *msg = yices_error_string();
  throwException(jenv, "java/lang/IllegalArgumentException", msg);
  goto out;
}
if ((*jenv)->ExceptionCheck(jenv)) {
   goto out;
}
printf("Size of yval vector: %d\n", s_arg4.size);
fflush(stdout);
size_t sz = s_arg4.size;
sz++; //increase by one for default value
sz = sz*2; //Need two values for each yval_t
sz = sz +0; // Memory should be correctly allocated, but deliberatly increasing size seems to partially alleviate the issue
/**
* Memory needed should be (yval_vetctor_t.size + 1 (default value) ) and then times 2 because each yval is represented by two ints.
*/
printf("Allocating memory for %lu ints.\n", sz);
fflush(stdout);
jint *jarr = malloc(sizeof(jint) * sz);
if (jarr == NULL) {
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Yices");
    goto out;
}
yval_t *data = s_arg4.data;
jarr[0] = m_arg3->node_id;
jarr[1] = m_arg3->node_tag;
size_t i;
for (i = 0; i < s_arg4.size; i++) {
  printf("position is : %lu %d %d\n", i, data[i].node_id, data[i].node_tag);
  jarr[2+2*i] = data[i].node_id;
  jarr[2+2*i+1] = data[i].node_tag;
}
printf("I am a debug message\n");
fflush(stdout);
jretval = (*jenv)->NewIntArray(jenv, sz);
if (jretval != NULL) {
  (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, jarr);
}
free(jarr);
printf("I am a debug message too\n");
fflush(stdout);
out:
yices_delete_yval_vector(m_arg4);
printf("I am a debug message also\n");
fflush(stdout);
return jretval;
}
//node_id and nodetag split for retaining argment order for C call
DEFINE_FUNC(intArray, 1val_1expand_1mapping) WITH_FOUR_ARGS(jmodel, jnodeid, int, jnodetag)
printf("Expanding mapping of arity %d.\n", arg3);
fflush(stdout);
MODEL_ARG(1)
YVAL_ARG(2,2,4) // CHANGE
EMPTY_YVAL_ARRAY_ARG(3)
EMPTY_YVAL_ARG(4)
CALL4(int, val_expand_mapping)
jintArray jretval = NULL;
if(retval == -1){  
  const char *msg = yices_error_string();
  throwException(jenv, "java/lang/IllegalArgumentException", msg);
  goto out;
}
if ((*jenv)->ExceptionCheck(jenv)) {
   goto out;
}
jint *jarr = malloc(sizeof(jint) * (sz+1)*2);
if (jarr == NULL) {
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Yices");
    goto out;
}
size_t i;
for (i = 0; i < sz; i++) {
  jarr[2*i] = m_arg3[i].node_id;
  jarr[2*i+1] = m_arg3[i].node_tag;
}
jarr[2*sz] = m_arg4->node_id;
jarr[2*sz+1] = m_arg4->node_tag;
jretval = (*jenv)->NewIntArray(jenv, sz);
if (jretval != NULL) {
  (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, jarr);
}
free(jarr);
out:
free(m_arg3);
return jretval;
}


DEFINE_FUNC(jterm, 1get_1value_1as_1term) WITH_TWO_ARGS(jmodel, jterm)
MODEL_ARG(1)
TERM_ARG(2)
CALL2(term_t, get_value_as_term)
TERM_RETURN

/*
 * TERM NAMING and PRINTING
 */

DEFINE_FUNC(int, 1set_1term_1name) WITH_TWO_ARGS(jterm, string)
TERM_ARG(1)
STRING_ARG(2)
CALL2(int, set_term_name)
FREE_STRING_ARG(2)
INT_RETURN

DEFINE_FUNC(string, 1get_1term_1name) WITH_ONE_ARG(jterm)
TERM_ARG(1)
CALL1(const char *, get_term_name)
STRING_RETURN

DEFINE_FUNC(jterm, 1get_1term_1by_1name) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, get_term_by_name)
FREE_STRING_ARG(1)
TERM_RETURN

//Creates String that needs to be freed
DEFINE_FUNC(string, 1term_1to_1string) WITH_FOUR_ARGS(jterm, int, int ,int)
TERM_ARG(1)
UINT32_ARG(2)
UINT32_ARG(3)
UINT32_ARG(4)
CALL4(char *, term_to_string)
STRING_RETURN

DEFINE_FUNC(string, 1type_1to_1string) WITH_FOUR_ARGS(jtype, int, int ,int)
TYPE_ARG(1)
UINT32_ARG(2)
UINT32_ARG(3)
UINT32_ARG(4)
CALL4(char *, type_to_string)
STRING_RETURN

DEFINE_FUNC(string, 1model_1to_1string) WITH_FOUR_ARGS(jmodel, int, int ,int)
MODEL_ARG(1)
UINT32_ARG(2)
UINT32_ARG(3)
UINT32_ARG(4)
CALL4(char *, model_to_string)
STRING_RETURN

DEFINE_FUNC(jterm, 1parse_1term) WITH_ONE_ARG(string)
STRING_ARG(1)
CALL1(term_t, parse_term)
FREE_STRING_ARG(1)
TERM_RETURN

/*
 * Functions for version checking
 */

DEFINE_FUNC(int, 1get_1version) WITHOUT_ARGS
return __YICES_VERSION;
}

DEFINE_FUNC(int, 1get_1major_1version) WITHOUT_ARGS
return __YICES_VERSION_MAJOR;
}

DEFINE_FUNC(int, 1get_1patch_1level) WITHOUT_ARGS
return __YICES_VERSION_PATCHLEVEL;
}
