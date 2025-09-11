// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import java.util.function.Supplier;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;

@SuppressWarnings({"unused", "checkstyle:methodname", "checkstyle:parametername"})
public final class Yices2NativeApi {
  private Yices2NativeApi() {}

  // Yices2 status codes
  public static final int YICES_STATUS_IDLE = 0;
  public static final int YICES_STATUS_SEARCHING = 1;
  public static final int YICES_STATUS_UNKNOWN = 2;
  public static final int YICES_STATUS_SAT = 3;
  public static final int YICES_STATUS_UNSAT = 4;
  public static final int YICES_STATUS_INTERRUPTED = 5;
  public static final int YICES_STATUS_ERROR = 6;

  // Yices2 term constructors
  public static final int YICES_CONSTRUCTOR_ERROR = -1;
  public static final int YICES_BOOL_CONST = 0;
  public static final int YICES_ARITH_CONST = 1;
  public static final int YICES_BV_CONST = 2;
  public static final int YICES_SCALAR_CONST = 3; // NOT used in JavaSMT
  public static final int YICES_VARIABLE = 4;
  public static final int YICES_UNINTERPRETED_TERM = 5;

  public static final int YICES_ITE_TERM = 6; // if-then-else
  public static final int YICES_APP_TERM = 7; // application of an uninterpreted function
  public static final int YICES_UPDATE_TERM = 8; // function update
  public static final int YICES_TUPLE_TERM = 9; // tuple constructor
  public static final int YICES_EQ_TERM = 10; // equality
  public static final int YICES_DISTINCT_TERM = 11; // distinct t_1 ... t_n
  public static final int YICES_FORALL_TERM = 12; // quantifier
  public static final int YICES_LAMBDA_TERM = 13; // lambda
  public static final int YICES_NOT_TERM = 14; // (not t)
  public static final int YICES_OR_TERM = 15; // n-ary OR
  public static final int YICES_XOR_TERM = 16; // n-ary XOR

  public static final int YICES_BV_ARRAY = 17; // array of boolean terms
  public static final int YICES_BV_DIV = 18; // unsigned division
  public static final int YICES_BV_REM = 19; // unsigned remainder
  public static final int YICES_BV_SDIV = 20; // signed division
  public static final int YICES_BV_SREM = 21; // remainder in signed division (rounding to 0)
  public static final int YICES_BV_SMOD = 22; // remainder in signed division (rounding to
  // -infinity)
  public static final int YICES_BV_SHL = 23; // shift left (padding with 0)
  public static final int YICES_BV_LSHR = 24; // logical shift right (padding with 0)
  public static final int YICES_BV_ASHR = 25; // arithmetic shift right (padding with sign bit)
  public static final int YICES_BV_GE_ATOM = 26; // unsigned comparison: (t1 >= t2)
  public static final int YICES_BV_SGE_ATOM = 27; // signed comparison (t1 >= t2)
  public static final int YICES_ARITH_GE_ATOM = 28; // atom (t1 >= t2) for arithmetic terms: t2 is
  // always 0
  public static final int YICES_ARITH_ROOT_ATOM = 29; // atom (0 <= k <= root_count(p)) && (x r
  // root(p,k)) for r in <, <=, ==, !=, >, >=

  public static final int YICES_ABS = 30; // absolute value
  public static final int YICES_CEIL = 31; // ceil
  public static final int YICES_FLOOR = 32; // floor
  public static final int YICES_RDIV = 33; // real division (as in x/y)
  public static final int YICES_IDIV = 34; // integer division
  public static final int YICES_IMOD = 35; // modulo
  public static final int YICES_IS_INT_ATOM = 36; // integrality test: (is-int t)
  public static final int YICES_DIVIDES_ATOM = 37; // divisibility test: (divides t1 t2)

  // projections
  public static final int YICES_SELECT_TERM = 38; // tuple projection
  public static final int YICES_BIT_TERM = 39; // bit-select: extract the i-th bit of a bitvector

  // sums
  public static final int YICES_BV_SUM = 40; // sum of pairs a * t where a is a bitvector constant
  // (and t is a bitvector term)
  public static final int YICES_ARITH_SUM = 41; // sum of pairs a * t where a is a rational (and t
  // is an arithmetic term)

  // products
  public static final int YICES_POWER_PRODUCT = 42; // power products: (t1^d1 * ... * t_n^d_n)

  // Workaround as Yices misses some useful operators,
  // MAX_INT avoids collisions with existing constants
  public static final int YICES_AND = Integer.MAX_VALUE - 1;
  public static final int YICES_BV_MUL = Integer.MAX_VALUE - 2;
  public static final int YICES_ARRAY_EVAL = Integer.MAX_VALUE - 3;

  /*
   * Yices model tags
   */
  public static final int YVAL_UNKNOWN = 0;
  public static final int YVAL_BOOL = 1;
  public static final int YVAL_RATIONAL = 2;
  public static final int YVAL_ALGEBRAIC = 3;
  public static final int YVAL_BV = 4;
  public static final int YVAL_SCALAR = 5;
  public static final int YVAL_TUPLE = 6;
  public static final int YVAL_FUNCTION = 7;
  public static final int YVAL_MAPPING = 8;

  /*
   * Yices initialization and exit
   */

  /** Initializes Yices data structures. Needs to be called before doing anything else. */
  public static native void yices_init();

  /** Call at the end to free memory allocated by Yices. */
  public static native void yices_exit();

  /**
   * Perform a full reset of Yices
   *
   * <p>This function deletes all the terms and types defined in Yices and resets the symbol tables.
   * It also deletes all contexts, models, configuration descriptors, and other records allocated in
   * Yices.
   */
  public static native void yices_reset();

  /**
   * Frees the specified String. Several API functions build and return a character string that is
   * allocated by Yices. To avoid memory leaks, this string must be freed when it is no longer used
   * by calling this function.
   *
   * @param stringPtr The pointer to the String
   */
  public static native void free_string(long stringPtr);

  /*
   * Yices Version checking for test purposes
   */

  public static native int yices_get_version();

  public static native int yices_get_major_version();

  public static native int yices_get_patch_level();

  /*
   * Context/ Environment creation
   */

  public static native long yices_new_config();

  public static native void yices_free_config(long cfg);

  /**
   * Set option to specified value.
   *
   * @param cfg The configuration to set the option in.
   * @param option The option to set.
   * @param value The value that the option will be set to.
   */
  public static native void yices_set_config(long cfg, String option, String value);

  /**
   * Prepares a context configuration for the specified logic.
   *
   * @param cfg The configuration to be prepared
   * @param logic Name of the logic to prepare for or "NULL"
   * @return 0 if successful, -1 if an error occurred
   */
  public static native int yices_default_config_for_logic(long cfg, String logic);

  public static native long yices_new_context(long cfg);

  public static native void yices_free_context(long ctx);

  public static native void yices_context_enable_option(long ctx, String option);

  public static native void yices_context_disable_option(long ctx, String option);

  /*
   * Yices search params
   */

  public static native long yices_new_param_record();

  public static native int yices_set_param(long record, String name, String value);

  public static native void yices_default_params_for_context(long ctx, long record);

  public static native void yices_free_param_record(long record);

  /*
   * Yices type construction
   */
  public static native int yices_bool_type();

  public static native int yices_int_type();

  public static native int yices_real_type();

  /**
   * Constructs a bitvector type.
   *
   * @param size is the number of bits. It must be positive and no more than YICES_MAX_BVSIZE
   * @return bitvector type
   */
  public static native int yices_bv_type(int size);

  /**
   * Creates the function type (-> dom[0] … dom[n-1] range).
   *
   * @param n function arity (i.e., size of array dom)
   * @param dom array of domain types
   * @param range range type
   * @return function type of n-arity
   */
  public static native int yices_function_type(int n, int[] dom, int range);

  /*
   * Yices type tests
   */
  public static native boolean yices_type_is_bool(int t);

  public static native boolean yices_type_is_int(int t);

  public static native boolean yices_type_is_real(int t);

  /**
   * Checks if type is arithmetic (i.e., either integer or real).
   *
   * @param t Type to check
   * @return true if arithmetic, false otherwise
   */
  public static native boolean yices_type_is_arithmetic(int t);

  public static native boolean yices_type_is_bitvector(int t);

  public static native boolean yices_type_is_function(int t);

  /**
   * Tests if the first type is a subtype of the second.
   *
   * @param t1 The first type
   * @param t2 The second type
   * @return true if t1 is a subtype of t2, otherwise false
   */
  public static native boolean yices_test_subtype(int t1, int t2);

  /**
   * Tests if Type1 and Type2 are compatible.
   *
   * @param t1 The first type
   * @param t2 The second type
   * @return true if t1 and t2 are compatible, otherwise false
   */
  public static native boolean yices_compatible_types(int t1, int t2);

  /**
   * Size of bitvector.
   *
   * @param t Bitvector to get the size of
   * @return Number of bits in bitvector or 0 if an error occurred
   */
  public static native int yices_bvtype_size(int t);

  public static native int yices_type_num_children(int t);

  public static native int yices_type_child(int t, int index);

  public static native int[] yices_type_children(int t);

  /*
   * TERM CONSTRUCTION
   */

  public static native int yices_new_uninterpreted_term(int type);

  public static native int yices_new_variable(int type);

  public static native int yices_constant(int type, int index);

  public static native int yices_ite(int t_if, int t_then, int t_else);

  public static native int yices_eq(int t_1, int t_2);

  public static native int yices_neq(int t_1, int t_2);

  public static native int yices_distinct(int size, int[] terms);

  public static native int yices_application(int t, int size, int[] terms);

  public static native int yices_update(int t1, int size, int[] terms, int t2);

  public static native int yices_forall(int size, int[] terms, int t);

  public static native int yices_exists(int size, int[] terms, int t);

  public static native int yices_lambda(int size, int[] terms, int t);

  /*
   * Bool Terms
   */

  public static native int yices_true();

  public static native int yices_false();

  public static native int yices_not(int t);

  public static native int yices_and(int n, int[] arg);

  public static native int yices_and2(int t1, int t2);

  public static native int yices_and3(int t1, int t2, int t3);

  public static native int yices_or(int n, int[] arg);

  public static native int yices_or2(int t1, int t2);

  public static native int yices_or3(int t1, int t2, int t3);

  public static native int yices_xor(int n, int[] arg);

  public static native int yices_xor2(int t1, int t2);

  public static native int yices_xor3(int t1, int t2, int t3);

  public static native int yices_iff(int t1, int t2);

  public static native int yices_implies(int t1, int t2);

  /*
   * Arithmetic Terms
   */
  public static native int yices_zero();

  public static native int yices_int32(int value);

  public static native int yices_int64(long val);

  public static native int yices_rational32(int num, int den);

  public static native int yices_rational64(long num, long den);

  public static native int yices_parse_rational(String val);

  public static native int yices_parse_float(String val);

  public static native int yices_add(int t1, int t2);

  public static native int yices_sub(int t1, int t2);

  public static native int yices_neg(int t);

  public static native int yices_mul(int t1, int t2);

  public static native int yices_square(int t);

  public static native int yices_power(int t, int power);

  public static native int yices_division(int t1, int t2);

  public static native int yices_sum(int size, int[] terms);

  public static native int yices_product(int size, int[] terms);

  public static native int yices_poly_int32(int size, int[] coeff, int[] terms);

  public static native int yices_poly_int64(int size, long[] coeff, int[] terms);

  public static native int yices_abs(int t);

  public static native int yices_floor(int t);

  public static native int yices_ceil(int t);

  public static native int yices_idiv(int t1, int t2);

  public static native int yices_imod(int t1, int t2);

  public static native int yices_arith_eq_atom(int t1, int t2);

  public static native int yices_arith_neq_atom(int t1, int t2);

  public static native int yices_arith_geq_atom(int t1, int t2);

  public static native int yices_arith_leq_atom(int t1, int t2);

  public static native int yices_arith_gt_atom(int t1, int t2);

  public static native int yices_arith_lt_atom(int t1, int t2);

  public static native int yices_arith_eq0_atom(int t);

  public static native int yices_arith_neq0_atom(int t);

  public static native int yices_arith_geq0_atom(int t);

  public static native int yices_arith_leq0_atom(int t);

  public static native int yices_arith_gt0_atom(int t);

  public static native int yices_arith_lt0_atom(int t);

  public static native int yices_divides_atom(int t1, int t2);

  public static native int yices_is_int_atom(int t);

  /*
   * Bitvector Terms
   */
  public static native int yices_bvconst_uint32(int size, int value);

  public static native int yices_bvcinst_uint64(int size, long value);

  public static native int yices_bvconst_int32(int size, int value);

  public static native int yices_bvconst_int64(int size, long value);

  public static native int yices_bvconst_zero(int size);

  public static native int yices_bvconst_one(int size);

  public static native int yices_bvconst_minus_one(int size);

  /**
   * Parses the given Array in little endian order values[0] becomes the least significant bit.
   * values[size-1] becomes the most significant bit.
   */
  public static native int yices_bvconst_from_array(int size, int[] values);

  public static native int yices_parse_bvbin(String value);

  public static native int yices_parse_bvhex(String value);

  public static native int yices_bvadd(int t1, int t2);

  public static native int yices_bvsub(int t1, int t2);

  public static native int yices_bvneg(int t);

  public static native int yices_bvmul(int t1, int t2);

  public static native int yices_bvsquare(int t);

  public static native int yices_bvpower(int t, int power);

  public static native int yices_bvsum(int size, int[] terms);

  public static native int yices_bvproduct(int size, int[] terms);

  public static native int yices_bvdiv(int t1, int t2);

  public static native int yices_bvrem(int t1, int t2);

  public static native int yices_bvsdiv(int t1, int t2);

  public static native int yices_bvsrem(int t1, int t2);

  public static native int yices_bvsmod(int t1, int t2);

  public static native int yices_bvnot(int t);

  public static native int yices_bvand(int size, int[] terms);

  public static native int yices_bvand2(int t1, int t2);

  public static native int yices_bvand3(int t1, int t2, int t3);

  public static native int yices_bvor(int size, int[] terms);

  public static native int yices_bvor2(int t1, int t2);

  public static native int yices_bvor3(int t1, int t2, int t3);

  public static native int yices_bvxor(int size, int[] terms);

  public static native int yices_bvxor2(int t1, int t2);

  public static native int yices_bvxor3(int t1, int t2, int t3);

  public static native int yices_bvnand(int t1, int t2);

  public static native int yices_bvnor(int t1, int t2);

  public static native int yices_bvxnor(int t1, int t2);

  public static native int yices_shift_left0(int t, int shift);

  public static native int yices_shift_left1(int t, int shift);

  public static native int yices_shift_right0(int t, int shift);

  public static native int yices_shift_right1(int t, int shift);

  public static native int yices_ashift_right(int t, int shift);

  public static native int yices_rotate_left(int t, int shift);

  public static native int yices_rotate_right(int t, int shift);

  public static native int yices_bvshl(int t1, int t2);

  public static native int yices_bvlshr(int t1, int t2);

  public static native int yices_bvashr(int t1, int t2);

  public static native int yices_bvextract(int t, int limit1, int limit2);

  public static native int yices_bitextract(int t, int pos);

  public static native int yices_bvconcat(int size, int[] terms);

  public static native int yices_bvconcat2(int t1, int t2);

  public static native int yices_bvrepeat(int t, int times);

  public static native int yices_sign_extend(int t, int times);

  public static native int yices_zero_extend(int t, int times);

  public static native int yices_redand(int t);

  public static native int yices_redor(int t);

  public static native int yices_redcomp(int t1, int t2);

  public static native int yices_bvarray(int size, int[] terms);

  public static native int yices_bveq_atom(int t1, int t2);

  public static native int yices_bvneq_atom(int t1, int t2);

  public static native int yices_bvge_atom(int t1, int t2);

  public static native int yices_bvgt_atom(int t1, int t2);

  public static native int yices_bvle_atom(int t1, int t2);

  public static native int yices_bvlt_atom(int t1, int t2);

  public static native int yices_bvsge_atom(int t1, int t2);

  public static native int yices_bvsgt_atom(int t1, int t2);

  public static native int yices_bvsle_atom(int t1, int t2);

  public static native int yices_bvslt_atom(int t1, int t2);

  /*
   * Term properties
   */
  public static native int yices_type_of_term(int t);

  public static native boolean yices_term_is_bool(int t);

  public static native boolean yices_term_is_int(int t);

  public static native boolean yices_term_is_real(int t);

  public static native boolean yices_term_is_arithmetic(int t);

  public static native boolean yices_term_is_bitvector(int t);

  public static native boolean yices_term_is_function(int t);

  public static native int yices_term_bitsize(int t);

  public static native boolean yices_term_is_ground(int t);

  public static native boolean yices_term_is_atomic(int t);

  public static native boolean yices_term_is_composite(int t);

  public static native boolean yices_term_is_projection(int t);

  public static native boolean yices_term_is_sum(int t);

  public static native boolean yices_term_is_bvsum(int t);

  public static native boolean yices_term_is_product(int t);

  public static native int yices_term_constructor(int t);

  public static native int yices_term_num_children(int t);

  public static native int yices_term_child(int t, int index);

  public static native int yices_proj_index(int t);

  public static native int yices_proj_arg(int t);

  public static native boolean yices_bool_const_value(int t);

  // TODO Return bool[] instead of int[]?
  /** Returns in little endian order. */
  public static native int[] yices_bv_const_value(int t, int bitsize);

  public static native String yices_rational_const_value(int t);

  /**
   * Returns i-th sum component of term t as String-Array [coefficient, term]. If t is in a form
   * like 3+x, for i = 0 the returned term will be -1/NULL_TERM.
   */
  public static native String[] yices_sum_component(int t, int i);

  /**
   * Returns the i-th component of a bvsum. Returned array has length bitsize+1. array[0] to
   * array[array.length-2] contain the coefficient, array[array.length-1] the term. If the t is in a
   * form like [101]+x, for i = 0, the returned term will be -1/NULL_TERM.
   */
  public static native int[] yices_bvsum_component(int t, int i, int bitsize);

  // TODO can return up to UINT32_MAX ?
  //  Daniel: we cast the uint return of exp to signed int (jint), this is obviously wrong!
  /**
   * Returns an array of size 2 in the form [term,exp] for the term and exponent at index i and
   * checks automatically for errors (original function return) and throws IllegalArgumentException
   * for return value -1. Original API: int32_t yices_product_component(term_t t, int32_t i, term_t
   * *term, uint32_t *exp) Component of a power product. A product t is of the form t0^d0 × … ×
   * tn^dn. This function stores the term ti into *term and the exponent di into *exp. The function
   * returns -1 if t is not a product or if the index i is too large. It returns 0 otherwise.
   */
  public static native int[] yices_product_component(int t, int i);

  /*
   * SAT Checking
   */
  public static native int yices_context_status(long ctx);

  public static native void yices_assert_formula(long ctx, int f);

  public static native void yices_assert_formulas(long ctx, int size, int[] formulas);

  /**
   * @param params Set to 0 for default search parameters.
   */
  public static native int yices_check_context(long ctx, long params);

  public static native void yices_stop_search(long ctx);

  public static native void yices_reset_context(long ctx);

  public static native int yices_assert_blocking_clause(long ctx);

  public static native void yices_push(long ctx);

  public static native void yices_pop(long ctx);

  /**
   * @param params Set to 0 for default search parameters.
   */
  public static native int yices_check_context_with_assumptions(
      long ctx, long params, int size, int[] terms);

  public static native int[] yices_get_unsat_core(long ctx);

  /**
   * @param params Set to 0 for default search parameters.
   */
  public static boolean yices_check_sat(long ctx, long params, ShutdownNotifier shutdownNotifier)
      throws IllegalStateException, InterruptedException {
    return satCheckWithShutdownNotifier(
        () -> yices_check_context(ctx, params), ctx, shutdownNotifier);
  }

  /**
   * @param params Set to 0 for default search parameters.
   */
  public static boolean yices_check_sat_with_assumptions(
      long ctx, long params, int size, int[] assumptions, ShutdownNotifier shutdownNotifier)
      throws InterruptedException {
    return satCheckWithShutdownNotifier(
        () -> yices_check_context_with_assumptions(ctx, params, size, assumptions),
        ctx,
        shutdownNotifier);
  }

  @SuppressWarnings("try")
  private static boolean satCheckWithShutdownNotifier(
      Supplier<Integer> satCheck, long pCtx, ShutdownNotifier shutdownNotifier)
      throws InterruptedException {
    int result;
    try (ShutdownHook hook = new ShutdownHook(shutdownNotifier, () -> yices_stop_search(pCtx))) {
      shutdownNotifier.shutdownIfNecessary();
      result = satCheck.get(); // the expensive computation
    }
    shutdownNotifier.shutdownIfNecessary();
    return check_result(result);
  }

  private static boolean check_result(int result) {
    switch (result) {
      case YICES_STATUS_SAT:
        return true;
      case YICES_STATUS_UNSAT:
        return false;
      default:
        // TODO Further ERROR CLARIFICATION
        String code = (result == YICES_STATUS_UNKNOWN) ? "\"unknown\"" : result + "";
        throw new IllegalStateException("Yices check returned:" + code);
    }
  }

  /*
   * Model generation and exploration
   */

  public static native long yices_get_model(long ctx, int keepSubst);

  public static native long yices_model_from_map(int size, int[] var, int[] constant);

  /*
   * renamed collect_defined_terms to def_terms as it caused an UnsatisfiedLinkError for some reason
   */
  public static native int[] yices_def_terms(long model); // collect_defined_terms(long model);

  public static native void yices_free_model(long model);

  /** get the value of a term as pair [node_id, node_tag]. */
  public static native int[] yices_get_value(long m, int t);

  public static native int yices_val_bitsize(long m, int id, int tag);

  public static native int yices_val_function_arity(long m, int id, int tag);

  public static native boolean yices_val_get_bool(long m, int id, int tag);

  public static native String yices_val_get_mpq(long m, int id, int tag);

  /*
   * node_id / node_tag separated to preserve C call order
   * Returns in little endian order
   */
  public static native int[] yices_val_get_bv(long m, int id, int size, int tag);

  /**
   * Returns array of yval_t values built like this: [yval_t.node_id, yval_t.node_tag,
   * yval_t.node_id, yval_t.node_tag, ...]. The first pair of values represent the default value,
   * the following values should represent mappings, which can be expanded using expand_mapping().
   */
  public static native int[] yices_val_expand_function(long m, int id, int tag);

  /**
   * Returns array of yval_t values built like this: [yval_t.node_id, yval_t.node_tag,
   * yval_t.node_id, yval_t.node_tag, ...]. The last pair of values represent the function's value,
   * the other pairs are values for the function's arguments. node_id / node_tag separated to
   * preserve C call order
   */
  public static native int[] yices_val_expand_mapping(long m, int id, int arity, int tag);

  /** get the value of a term as (constant) term. */
  public static native int yices_get_value_as_term(long m, int t);

  public static native void yices_set_term_name(int t, String name);

  public static native String yices_get_term_name(int t);

  public static native int yices_get_term_by_name(String name);

  /**
   * Use to print a term in a readable format. Result will be truncated if height/width of the
   * String are too small.
   *
   * @param t The term to print
   * @param width The width of the resulting String
   * @param height The height/lines of resulting String
   */
  private static native String yices_term_to_string(int t, int width, int height, int offset);

  private static native String yices_type_to_string(int t, int width, int height, int offset);

  private static native String yices_model_to_string(long m, int width, int height, int offset);

  public static String yices_term_to_string(int t) {
    return yices_term_to_string(t, Integer.MAX_VALUE, 1, 0);
  }

  public static String yices_type_to_string(int t) {
    return yices_type_to_string(t, Integer.MAX_VALUE, 1, 0);
  }

  public static String yices_model_to_string(long m) {
    return yices_model_to_string(m, Integer.MAX_VALUE, 1, 0);
  }

  /**
   * Parse a single expression/term in SMTLIB2-based Yices input language.
   *
   * <p>Declarations of symbols not are allowed. All symbols must already be known.
   */
  public static native int yices_parse_term(String t);

  public static native int yices_subst_term(int size, int[] from, int[] to, int t);

  /**
   * @return int 1 if the Yices2-lib is compiled thread-safe and 0 otherwise
   */
  public static native int yices_is_thread_safe();

  /** The function first checks whether f is satisifiable or unsatisfiable. */
  public static native int yices_check_formula(int term, String logic, long model, String delegate);

  /**
   * This is similar to yices_check_formula except that it checks whether the conjunction of f[0]
   * ... f[n-1] is satisfiable.
   */
  public static native int yices_check_formulas(
      int[] terms, int n, String logic, long model, String delegate);

  /**
   * @return int 1 if delegate(SAT-Solver) available for use, 0 otherwise
   */
  public static native int yices_has_delegate(String delegate);

  /**
   * @return type of a function node
   */
  public static native int yices_val_function_type(long model, int id, int tag);

  /**
   * @return term_vector (NOT int with error code) that is supported. Empty if error!
   */
  public static native int[] yices_model_term_support(long model, int term);
}
