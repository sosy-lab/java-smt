/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.z3;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import javax.annotation.Nullable;

/** This class contains the native calls for Z3.
 *
 * <p>Z3 uses reference-counting for all objects. If a function returns an
 * object and the user wants to use it only once, the reference-counter
 * should not be incremented. The object will be destroyed after next usage.
 * If the user wants to use the object several times, he has to increment
 * the reference (only once!), so that the object remains valid. */
@SuppressWarnings({
  "unused",
  "checkstyle:methodname",
  "checkstyle:parametername",
  "checkstyle:parameternumber"
})
final class Z3NativeApi {
  private Z3NativeApi() {}

  // Helper Classes,
  // they are used during the native operations
  // and can be accessed later to get the values.
  static class PointerToInt {
    @SuppressFBWarnings(value = "UUF_UNUSED_FIELD", justification = "Read by native code")
    int value;
  }

  static class PointerToLong {
    @SuppressFBWarnings(value = "UUF_UNUSED_FIELD", justification = "Read by native code")
    long value;
  }

  static class PointerToString {
    @SuppressFBWarnings(value = "UUF_UNUSED_FIELD", justification = "Read by native code")
    @Nullable
    String value;
  }

  /**
   * Create a new optimize context.
   *
   * <p>User must use {@link #optimize_inc_ref}
   * and {@link #optimize_dec_ref} to manage optimize objects.
   * Even if the context was created using
   * {@link #mk_context} instead of {@link #mk_context_rc}.
   *
   * @param context Z3_context pointer
   * @return Z3_optimize pointer.
   */
  static native long mk_optimize(long context);

  /**
   * Increment the reference counter of the optimize context.
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   */
  static native void optimize_inc_ref(long context, long optimize);

  /**
   * Decrement the reference counter of the optimize context.
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   */
  static native void optimize_dec_ref(long context, long optimize);

  /**
   * Add a maximization constraint.
   *
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   * @param ast Z3_ast arithmetical term to maximize.
   * @return objective index
   */
  static native int optimize_maximize(long context, long optimize, long ast);

  /**
   * Add a minimization constraint.
   *
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   * @param ast Z3_ast arithmetical term to maximize.
   * @return objective index
   */
  static native int optimize_minimize(long context, long optimize, long ast);

  /**
   * Check consistency and produce optimal values.
   *
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   * @return status as {@link Z3NativeApiConstants.Z3_LBOOL}:
   *   false, undefined or true.
   */
  static native int optimize_check(long context, long optimize) throws Z3SolverException;

  /**
   * Retrieve a string that describes the last status returned by
   * {@link #optimize_check}.
   * Use this method when #Z3_optimize_check returns Z3_L_UNDEF.
   *
   * @param c Z3_context
   * @param d Z3_optimize
   */
  static native String optimize_get_reason_unknown(long c, long d);

  /**
   * \brief Retrieve the model for the last #Z3_optimize_check
   * The error handler is invoked if a model is not available because
   * the commands above were not invoked for the given optimization
   * solver, or if the result was \c Z3_L_FALSE.
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   * @return Z3_model pointer
   */
  static native long optimize_get_model(long context, long optimize);

  /**
   * Assert hard constraint to the optimization context.
   *
   * @param context Z3_context pointer
   * @param optimize Z3_optimize pointer
   * @param ast Z3_ast imposed constraints
   */
  static native void optimize_assert(long context, long optimize, long ast);

  /**
   * Create a backtracking point.
   *
   * <p>The optimize solver contains a set of rules, added facts and assertions.
   * The set of rules, facts and assertions are restored upon calling {#link #optimize_pop}
   *
   * @param c Z3_context
   * @param d Z3_optimize
   */
  static native void optimize_push(long c, long d);

  /**
   * Backtrack one level.
   * The number of calls to pop cannot exceed calls to push.
   *
   * @param c Z3_context
   * @param d Z3_optimize
   */
  static native void optimize_pop(long c, long d);

  /**
   * Set parameters on optimization context.
   *
   * @param c Z3_context context
   * @param o Z3_optimize optimization context
   * @param p Z3_params parameters
   */
  static native void optimize_set_params(long c, long o, long p);

  /**
   * Return the parameter description set for the given optimize object.
   *
   * @param c Z3_context context
   * @param o Z3_optimize optimization context
   * @return Z3_param_descrs
   */
  static native long optimize_get_param_descrs(long c, long o);

  /**
   * Retrieve lower bound value or approximation for the i'th optimization objective.
   *
   * @param c Z3_context context
   * @param o Z3_optimize optimization context
   * @param idx index of optimization objective
   *
   * @return Z3_ast
   */
  static native long optimize_get_lower(long c, long o, int idx);

  /**
   * Retrieve upper bound value or approximation for the i'th optimization objective.
   *
   * @param c Z3_context context
   * @param o Z3_optimize optimization context
   * @param idx index of optimization objective
   *
   * @return Z3_ast
   */
  static native long optimize_get_upper(long c, long o, int idx);

  /**
   * @param c Z3_context context.
   * @param o Z3_optimize optimization context.
   * @return Current context as a string.
   */
  static native String optimize_to_string(long c, long o);

  /**
   * @param c Z3_context
   * @param t Z3_optimize
   * @return Description of parameters accepted by optimize
   */
  static native String optimize_get_help(long c, long t);

  /**
   * Retrieve statistics information from the last call to {@link #optimize_check}
   *
   * @return Z3_stats
   */
  static native long optimize_get_statistics(long c, long d);

  /** -- end optimization -- **/

  // CREATE CONFIGURATION
  static native void global_param_set(String param_id, String param_value);

  static native void global_param_reset_all();

  static native boolean global_param_get(String param_id, PointerToString param_value);

  static native long mk_config();

  static native void del_config(long context);

  static native void set_param_value(long z3_config, String param_id, String param_value);

  // CREATE CONTEXT
  static native long mk_context(long config);

  static native long mk_context_rc(long config);

  static native void del_context(long context);

  static native void inc_ref(long context, long ast);

  static native void dec_ref(long context, long ast);

  static native void update_param_value(long context, String param_id, String param_value);

  static native boolean get_param_value(long context, String param_id, PointerToString param_value);

  /**
   * Interrupt the execution of a Z3 procedure.
   * This procedure can be used to interrupt: solvers, simplifiers and tactics.
   *
   * @param context Z3_context
   */
  static native void interrupt(long context);

  // PARAMETERS
  static native long mk_params(long context);

  static native void params_inc_ref(long context, long params);

  static native void params_dec_ref(long context, long params);

  static native void params_set_bool(long context, long params, long symbol, boolean value);

  static native void params_set_uint(long context, long params, long symbol, int value);

  static native void params_set_double(long context, long params, long symbol, double value);

  static native void params_set_symbol(long context, long params, long symbol, long symbol_value);

  static native String params_to_string(long context, long params);

  static native void params_validate(long context, long params, long params_descrs);

  // PARAMETER DESCRIPTIONS
  static native void param_descrs_inc_ref(long context, long params_descrs);

  static native void param_descrs_dec_ref(long context, long params_descrs);

  static native int param_descrs_get_kind(long context, long params_descrs, long symbol);

  static native int param_descrs_size(long context, long params_descrs);

  static native long param_descrs_get_name(long context, long params_descrs, int index);

  static native String param_descrs_to_string(long context, long params_descrs);

  // SYMBOLS
  static native long mk_int_symbol(long context, int number);

  static native long mk_string_symbol(long context, String name);

  // SORTS
  static native long mk_uninterpreted_sort(long context, long symbol);

  static native long mk_bool_sort(long context);

  static native long mk_int_sort(long context);

  static native long mk_real_sort(long context);

  static native long mk_bv_sort(long context, int size);

  static native long mk_finite_domain_sort(long context, long symbol, long size);

  static native long mk_array_sort(long context, long sort1, long sort2);

  static native long mk_tuple_sort(
      long context,
      long symbol,
      int len,
      long[] symbols,
      long[] sorts,
      PointerToLong tupl_decl,
      long[] proj_decl);

  static native long mk_enumeration_sort(
      long context, long symbol, int len, long[] symbols, long[] enum_consts, long[] enum_testers);

  static native long mk_list_sort(
      long context,
      long symbol,
      long sort,
      PointerToLong nil_decl,
      PointerToLong is_nil_decl,
      PointerToLong cons_decl,
      PointerToLong is_cons_decl,
      PointerToLong head_decl,
      PointerToLong tail_decl);

  static native long mk_constructor(
      long context,
      long symbol,
      long recognizer,
      int len,
      long[] symbols,
      long[] sorts,
      int[] sort_refs);

  static native void del_constructor(long context, long constructor);

  static native long mk_datatype(long context, long symbol, int len, long[] constructors);

  static native long mk_constructor_list(long context, int len, long[] constructors);

  static native void del_constructor_list(long context, long constructor);

  static native void mk_datatypes(
      long context, int len, long[] symbols, long[] sorts, long[] constructor_lists);

  static native void query_constructor(
      long context,
      long constructor,
      int len,
      PointerToLong constructor2,
      PointerToLong tester,
      long[] accessors);

  // CONSTANTS AND APPLICATIONS

  /**
   * @return Z3_func_decl
   */
  private static native long mk_func_decl(
      long context, long symbol, int len, long[] sorts, long sort);

  private static native long mk_app(long context, long decl, int len, long[] args);

  static native long mk_const(long context, long symbol, long sort);

  static native long mk_fresh_func_decl(
      long context, String prefix, int len, long[] sorts, long sort);

  static native long mk_fresh_const(long context, String prefix, long sort);

  static long mk_func_decl(long context, long symbol, long[] sorts, long sort) {
    return mk_func_decl(context, symbol, sorts.length, sorts, sort);
  }

  static long mk_app(long context, long decl, long... args) {
    return mk_app(context, decl, args.length, args);
  }

  // PROPOSITIONAL LOGIC AND EQUALITY
  static native long mk_true(long context);

  static native long mk_false(long context);

  static native long mk_eq(long context, long a1, long a2);

  private static native long mk_distinct(long context, int len, long[] as);

  static native long mk_not(long context, long a1);

  static native long mk_ite(long context, long a1, long a2, long a3);

  static native long mk_iff(long context, long a1, long a2);

  static native long mk_implies(long context, long a1, long a2);

  static native long mk_xor(long context, long a1, long a2);

  static native long mk_and(long context, int len, long[] as);

  static native long mk_or(long context, int len, long[] as);

  static long mk_distinct(long context, long... as) {
    return mk_distinct(context, as.length, as);
  }

  static long mk_and(long context, long... as) {
    return mk_and(context, as.length, as);
  }

  static long mk_or(long context, long... as) {
    return mk_or(context, as.length, as);
  }

  // ARITHMETIC: INTEGERS AND REALS
  static native long mk_add(long context, int len, long[] as);

  private static native long mk_mul(long context, int len, long[] as);

  private static native long mk_sub(long context, int len, long[] as);

  static native long mk_unary_minus(long context, long a1);

  static native long mk_div(long context, long a1, long a2);

  static native long mk_mod(long context, long a1, long a2);

  static native long mk_rem(long context, long a1, long a2);

  static native long mk_power(long context, long a1, long a2);

  static native long mk_lt(long context, long a1, long a2);

  /**
   * Create less than or equal to.
   * The nodes {@code t1} and {@code t2} must have the same sort, and must be
   * int or real.
   */
  static native long mk_le(long context, long a1, long a2);

  static native long mk_gt(long context, long a1, long a2);

  static native long mk_ge(long context, long a1, long a2);

  static native long mk_int2real(long context, long a1);

  static native long mk_real2int(long context, long a1);

  static native long mk_is_int(long context, long a1);

  static long mk_add(long context, long... as) {
    return mk_add(context, as.length, as);
  }

  static long mk_mul(long context, long... as) {
    return mk_mul(context, as.length, as);
  }

  static long mk_sub(long context, long... as) {
    return mk_sub(context, as.length, as);
  }

  // BIT-VECTORS
  static native long mk_bvnot(long context, long a1);

  static native long mk_bvredand(long context, long a1);

  static native long mk_bvredor(long context, long a1);

  static native long mk_bvand(long context, long a1, long a2);

  static native long mk_bvor(long context, long a1, long a2);

  static native long mk_bvxor(long context, long a1, long a2);

  static native long mk_bvnand(long context, long a1, long a2);

  static native long mk_bvnor(long context, long a1, long a2);

  static native long mk_bvxnor(long context, long a1, long a2);

  static native long mk_bvneg(long context, long a1);

  static native long mk_bvadd(long context, long a1, long a2);

  static native long mk_bvsub(long context, long a1, long a2);

  static native long mk_bvmul(long context, long a1, long a2);

  static native long mk_bvudiv(long context, long a1, long a2);

  static native long mk_bvsdiv(long context, long a1, long a2);

  static native long mk_bvurem(long context, long a1, long a2);

  static native long mk_bvsrem(long context, long a1, long a2);

  static native long mk_bvsmod(long context, long a1, long a2);

  static native long mk_bvult(long context, long a1, long a2);

  static native long mk_bvslt(long context, long a1, long a2);

  static native long mk_bvule(long context, long a1, long a2);

  static native long mk_bvsle(long context, long a1, long a2);

  static native long mk_bvuge(long context, long a1, long a2);

  static native long mk_bvsge(long context, long a1, long a2);

  static native long mk_bvugt(long context, long a1, long a2);

  static native long mk_bvsgt(long context, long a1, long a2);

  static native long mk_concat(long context, long a1, long a2);

  static native long mk_extract(long context, int high, int low, long a1);

  static native long mk_sign_ext(long context, int i, long a1);

  static native long mk_zero_ext(long context, int i, long a1);

  static native long mk_repeat(long context, int i, long a1);

  static native long mk_bvshl(long context, long a1, long a2);

  static native long mk_bvlshr(long context, long a1, long a2);

  static native long mk_bvashr(long context, long a1, long a2);

  static native long mk_rotate_left(long context, int i, long a1);

  static native long mk_rotate_right(long context, int i, long a1);

  static native long mk_ext_rotate_left(long context, long a1, long a2);

  static native long mk_ext_rotate_right(long context, long a1, long a2);

  static native long mk_bv2int(long context, long a1, boolean is_signed);

  static native long mk_int2bv(long context, int len, long a1);

  static native long mk_bvadd_no_overflow(long context, long a1, long a2, boolean is_signed);

  static native long mk_bvadd_no_underflow(long context, long a1, long a2);

  static native long mk_bvsub_no_overflow(long context, long a1, long a2);

  static native long mk_bvsub_no_underflow(long context, long a1, long a2, boolean is_signed);

  static native long mk_bvsdiv_no_overflow(long context, long a1, long a2);

  static native long mk_bvneg_no_overflow(long context, long a1);

  static native long mk_bvmul_no_overflow(long context, long a1, long a2, boolean is_signed);

  static native long mk_bvmul_no_underflow(long context, long a1, long a2);

  // ARRAYS
  static native long mk_select(long context, long a, long i);

  static native long mk_store(long context, long a, long i, long v);

  static native long mk_const_array(long context, long sort, long v);

  static native long mk_map(long context, long func_decl, int n, long[] args);

  static native long mk_array_default(long context, long a1);

  // SETS
  static native long mk_set_sort(long context, long sort);

  static native long mk_empty_set(long context, long sort);

  static native long mk_full_set(long context, long sort);

  static native long mk_set_add(long context, long a1, long a2);

  static native long mk_set_del(long context, long a1, long a2);

  static native long mk_set_union(long context, int len, long[] a1);

  static native long mk_set_intersect(long context, int len, long[] a1);

  static native long mk_set_difference(long context, long a1, long a2);

  static native long mk_set_complement(long context, long a1);

  static native long mk_set_member(long context, long a1, long a2);

  static native long mk_set_subset(long context, long a1, long a2);

  // NUMERALS
  static native long mk_numeral(long context, String s, long sort);

  static native long mk_real(long context, int num, int den);

  static native long mk_int(long context, int v, long sort);

  static native long mk_unsigned_int(long context, int v, long sort);

  static native long mk_int64(long context, long v, long sort);

  static native long mk_unsigned_int64(long context, long v, long sort);

  // QUANTIFIERS

  /**
   * Create a pattern for quantifier instantiation.
   *
   * <p>Z3 uses pattern matching to instantiate quantifiers.
   * If a pattern is not provided for a quantifier, then Z3 will
   * automatically compute a set of patterns for it. However, for
   * optimal performance, the user should provide the patterns.
   *
   * <p>Patterns comprise a list of terms. The list should be
   * non-empty.  If the list comprises of more than one term, it is
   * a called a multi-pattern.
   *
   * <p>In general, one can pass in a list of (multi-)patterns in the
   * quantifier constructor.
   *
   * @param context Z3_context
   * @param terms Z3_ast[]
   * @return Z3_pattern
   */
  static native long mk_pattern(long context, int num_patterns, long[] terms);

  /**
   * Create a bound variable.
   *
   * <p>Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
   * the meaning of de-Bruijn indices by indicating the compilation process from
   * non-de-Bruijn formulas to de-Bruijn format.
   *
   * {@code
   * abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
   * abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
   * abs1(x, x, n) = b_n
   * abs1(y, x, n) = y
   * abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
   * abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
   * }
   *
   * <p>The last line is significant: the index of a bound variable is different depending
   * on the scope in which it appears. The deeper x appears, the higher is its
   * index.
   *
   * @param context Z3_context
   * @param index de-Bruijn index
   * @param ty Sort of the bound variable
   * @return Z3_ast
   */
  static native long mk_bound(long context, int index, long ty);

  /**
   * Create a forall formula.
   * It takes an expression {@code body} that contains bound variables
   * of the same sorts as the sorts listed in the array {@code sorts}.
   * The bound variables are de-Bruijn indices created
   * using {@link #mk_bound}.
   * The array {@code decl_names} contains the names that the quantified formula
   * used for the bound variables.
   *
   * <p>Z3 applies the convention that the last element in the {@code decl_names}
   * and {@code sorts} array refers to the variable with index 0,
   * the second to last element of {@code decl_names} and
   * {@code sorts} refers to the variable with index 1, etc.
   *
   * @param context Z3_context logical context
   * @param weight Weight quantifiers are associated with weights indicating
   *               the importance of using the quantifier during instantiation.
   *               By default, pass the weight 0.
   * @param num_patterns Number of patterns.
   * @param patterns Z3_pattern[] array containing the patterns created using
   *               {@link #mk_pattern}.
   * @param num_decls number of variables to be bound.
   * @param sorts Z3_sort[] the sorts of the bound variables.
   * @param decl_names Z3_symbol[] names of the bound variables.
   * @param body the body of the quantifier.
   */
  static native long mk_forall(
      long context,
      int weight,
      int num_patterns,
      long[] patterns,
      int num_decls,
      long[] sorts,
      long[] decl_names,
      long body);

  /**
   * Create an EXISTS-formula. Similar to {@link #mk_forall}.
   */
  static native long mk_exists(
      long context,
      int weight,
      int num_patterns,
      long[] patterns,
      int num_decls,
      long[] sorts,
      long[] decl_names,
      long body);

  /**
   * Create a quantifier - universal or existential, with pattern hints.
   * See the documentation for {@link #mk_forall} for an explanation of the
   * parameters.
   *
   * @param context Z3_context
   * @param weight quantifiers are associated with weights indicating the
   *               importance of using the quantifier during instantiation.
   *               By default, pass the weight 0.
   * @param patterns Z3_pattern[] array containing the patterns created using
   *  {@link #mk_pattern}.
   * @param sorts Z3_sort[] Array of sorts of the bound variables.
   * @param decl_names Z3_symbol[] Names of the bound variables.
   * @param body Body of the quantifier
   */
  static native long mk_quantifier(
      long context,
      boolean is_forall,
      int weight,
      int num_patterns,
      long[] patterns,
      int num_decls,
      long[] sorts,
      long[] decl_names,
      long body);

  /**
   * Create a quantifier - universal or existential, with pattern hints,
   * number of patterns, and attributes.
   *
   * @param context Z3_context
   * @param quantifier_id Z3_symbol identifier to identify a quantifier.
   * @param skolem_id Z3_symbol identifier to identify skolem constants
   *                  introduced by quantifier.
   * @param patterns Z3_pattern[]
   * @param sorts Z3_sort[]
   * @param decl_names Z3_symbol[]
   */
  static native long mk_quantifier_ex(
      long context,
      boolean is_forall,
      int weight,
      long quantifier_id,
      long skolem_id,
      int num_patterns,
      long[] patterns,
      int num_no_patterns,
      long[] no_patterns,
      int num_decls,
      long[] sorts,
      long[] decl_names,
      long body);

  /**
   * Create a universal quantifier using a list of constants that
   * will form the set of bound variables.
   *
   * @param context Z3_context
   * @param weight quantifiers are associated with weights indicating the
   *               importance of using
   *               the quantifier during instantiation. By default, pass the weight 0.
   * @param num_bound number of constants to be abstracted into bound variables.
   * @param bound Z3_app[] array of constants to be abstracted into
   *              bound variables.
   * @param num_patterns number of patterns.
   * @param patterns Z3_pattern[]
   */
  static native long mk_forall_const(
      long context,
      int weight,
      int num_bound,
      long[] bound,
      int num_patterns,
      long[] patterns,
      long body);

  /**
   * See {@link #mk_forall_const(long, int, int, long[], int, long[], long)};
   */
  static native long mk_exists_const(
      long context,
      int weight,
      int num_bound,
      long[] bound,
      int num_patterns,
      long[] patterns,
      long body);

  static native long mk_quantifier_const(
      long context,
      boolean is_forall,
      int weight,
      int num_bound,
      long[] bound,
      int num_patterns,
      long[] patterns,
      long body);

  static native long mk_quantifier_const_ex(
      long context,
      boolean is_forall,
      int weight,
      long quantifier_id,
      long skolem_id,
      int num_bound,
      long[] bound,
      int num_patterns,
      long[] patterns,
      int num_no_patterns,
      long[] no_patterns,
      long body);

  // ACCESSORS
  static native int get_symbol_kind(long context, long a1);

  static native int get_symbol_int(long context, long a1);

  static native String get_symbol_string(long context, long a1);

  static native long get_sort_name(long context, long a1);

  static native int get_sort_id(long context, long a1);

  static native long sort_to_ast(long context, long a1);

  static native boolean is_eq_sort(long context, long a1, long a2);

  static native int get_sort_kind(long context, long a1);

  static native int get_bv_sort_size(long context, long sort);

  static native boolean get_finite_domain_sort_size(long context, long a1, PointerToLong a2);

  static native long get_array_sort_domain(long context, long a1);

  static native long get_array_sort_range(long context, long a1);

  static native long get_tuple_sort_mk_decl(long context, long a1);

  static native int get_tuple_sort_num_fields(long context, long a1);

  static native long get_tuple_sort_field_decl(long context, long a1, int a2);

  static native int get_datatype_sort_num_constructors(long context, long a1);

  static native long get_datatype_sort_constructor(long context, long a1, int a2);

  static native long get_datatype_sort_recognizer(long context, long a1, int a2);

  static native long get_datatype_sort_constructor_accessor(long context, long a1, int a2, int a3);

  static native int get_relation_arity(long context, long a1);

  static native long get_relation_column(long context, long a1, int a2);

  static native long func_decl_to_ast(long context, long a1);

  static native boolean is_eq_func_decl(long context, long a1, long a2);

  static native int get_func_decl_id(long context, long a1);

  static native long get_decl_name(long context, long a1);

  /**
   * @param a1 Z3_func_decl
   * @return Z3_decl_kind
   */
  static native int get_decl_kind(long context, long a1);

  static native int get_domain_size(long context, long a1);

  static native int get_arity(long context, long a1);

  static native long get_domain(long context, long a1, int a2);

  static native long get_range(long context, long a1);

  static native int get_decl_num_parameters(long context, long a1);

  static native int get_decl_parameter_kind(long context, long a1, int a2);

  static native int get_decl_int_parameter(long context, long a1, int a2);

  static native double get_decl_double_parameter(long context, long a1, int a2);

  static native long get_decl_symbol_parameter(long context, long a1, int a2);

  static native long get_decl_sort_parameter(long context, long a1, int a2);

  static native long get_decl_ast_parameter(long context, long a1, int a2);

  static native long get_decl_func_decl_parameter(long context, long a1, int a2);

  static native String get_decl_rational_parameter(long context, long a1, int a2);

  static native long app_to_ast(long context, long a1);

  static native long get_app_decl(long context, long a1);

  static native int get_app_num_args(long context, long a1);

  /**
   * Precondition: {@code i < get_num_args(c, a)}
   * @return Z3_ast the i-th argument of the given application.
   */
  static native long get_app_arg(long context, long a1, int index);

  static native boolean is_eq_ast(long context, long a1, long a2);

  static native int get_ast_id(long context, long a1);

  static native int get_ast_hash(long context, long a1);

  static native long get_sort(long context, long a1);

  static native boolean is_well_sorted(long context, long a1);

  static native int get_bool_value(long context, long a1);

  /**
   * @return Z3_ast_kind
   */
  static native int get_ast_kind(long context, long a1);

  static native boolean is_app(long context, long a1);

  static native boolean is_numeral_ast(long context, long a1);

  static native boolean is_algebraic_number(long context, long a1);

  static native long to_app(long context, long a1);

  /**
   * @param a1 Z3_ast
   * @return Z3_func_decl
   */
  static native long to_func_decl(long context, long a1);

  static native String get_numeral_string(long context, long a1);

  static native String get_numeral_decimal_string(long context, long a1, int a2);

  /**
   * Return the numerator (as a numeral AST) of a numeral AST of sort Real.
   *
   * @param context z3_context
   * @param a1 Z3_ast
   * @return Z3_ast
   */
  static native long get_numerator(long context, long a1);

  /**
   * Return the denominator (as a numeral AST) of a numeral AST of sort Real.
   *
   * @param context z3_context
   * @param a1 Z3_ast
   * @return Z3_ast
   */
  static native long get_denominator(long context, long a1);

  static native boolean get_numeral_small(
      long context, long a1, PointerToLong a2, PointerToLong a3);

  static native boolean get_numeral_int(long context, long a1, PointerToInt a2);

  static native boolean get_numeral_uint(long context, long a1, PointerToInt a2);

  static native boolean get_numeral_uint64(long context, long a1, PointerToLong a2);

  static native boolean get_numeral_int64(long context, long a1, PointerToLong a2);

  static native boolean get_numeral_rational_int64(
      long context, long a1, PointerToLong a2, PointerToLong a3);

  static native long get_algebraic_number_lower(long context, long a1, int a2);

  static native long get_algebraic_number_upper(long context, long a1, int a2);

  static native long pattern_to_ast(long context, long a1);

  static native int get_pattern_num_terms(long context, long a1);

  static native long get_pattern(long context, long a1, int a2);

  /**
   * @param a1 Variable AST.
   * @return index of de-Brujin bound variable.
   */
  static native int get_index_value(long context, long a1);

  static native boolean is_quantifier_forall(long context, long a1);

  static native int get_quantifier_weight(long context, long a1);

  static native int get_quantifier_num_patterns(long context, long a1);

  static native long get_quantifier_pattern_ast(long context, long a1, int a2);

  static native int get_quantifier_num_no_patterns(long context, long a1);

  static native long get_quantifier_no_pattern_ast(long context, long a1, int a2);

  /**
   * @return number of bound variables of quantifier.
   */
  static native int get_quantifier_num_bound(long context, long a1);

  /**
   * Return symbol of the i'th bound variable.
   *
   * @return Z3_symbol
   */
  static native long get_quantifier_bound_name(long context, long a1, int i);

  /**
   * Returns sort of the i'th bound variable.
   *
   * @return Z3_sort
   */
  static native long get_quantifier_bound_sort(long context, long a1, int i);

  static native long get_quantifier_body(long context, long a1);

  static native long simplify(long context, long a1);

  static native long simplify_ex(long context, long a1, long a2);

  static native String simplify_get_help(long context);

  static native long simplify_get_param_descrs(long context);

  // MODIFIERS

  /**
   * Update the arguments of term {@code a} using the arguments {@code args}.
   * The number of arguments \c num_args should coincide
   * with the number of arguments to \c a.
   * If \c a is a quantifier, then num_args has to be 1.
   *
   * @param a1 Z3_ast
   * @param args Z3_ast[]
   *
   * @return Z3_ast
   */
  static native long update_term(long context, long a1, int num_exprs, long[] args);

  /**
   * Substitute every occurrence of <code>from[i]</code> in <code>a</code>
   * with <code>to[i]</code>, for <code>i</code> smaller than
   * <code>num_exprs</code>.
   * The result is the new AST. The arrays <code>from</code> and <code>to</code>
   * must have size <code>num_exprs</code>.
   * For every <code>i</code> smaller than <code>num_exprs</code>, we must have
   * that sort of <code>from[i]</code> must be equal to sort of
   * <code>to[i]</code>.
   *
   * @param context Z3_context
   * @param a Z3_ast Input formula
   * @param num_exprs Number of expressions to substitute
   * @param from Change from
   * @param to Change to
   * @return Formula with substitutions applied.
   */
  static native long substitute(long context, long a, int num_exprs, long[] from, long[] to);

  /**
   * Substitute the free variables in <code>a</code> with the expressions in
   * <code>to</code>.
   * For every <code>i</code> smaller than <code>num_exprs</code>, the variable
   * with de-Bruijn
   * index <code>i</code> is replaced with term <code>to[i]</code>.
   *
   * @param context Z3_context
   * @param a Z3_ast Input formula
   * @param num_exprs Number of expressions to substitute
   * @param to Change to
   * @return Formula with substitutions applied.
   */
  static native long substitute_vars(long context, long a, int num_exprs, long[] to);

  /**
   * Translate/Copy the AST {@code a} from context {@code contextSource} to
   * context {@code contextTarget}.
   * AST {@code a} must have been created using context {@code contextSource}.
   *
   * <p>Precondition: {@code contextSource != contextTarget}
   *
   * @param contextSource Z3_context
   * @param a Z3_ast
   * @param contextTarget Z3_context
   * @return Z3_ast
   */
  static native long translate(long contextSource, long a, long contextTarget);

  // MODELS
  static native void model_inc_ref(long context, long model);

  static native void model_dec_ref(long context, long model);

  /**
   * Evaluate the AST node {@code t} in the given model.
   * @return {@code true} if succeeded, and store the result in {@code v}.
   *
   * If {@code model_completion} is {@code true}, then Z3 will assign an
   * interpretation for any constant or function that does
   * not have an interpretation in {@code m}.
   * These constants and functions were essentially don't cares.
   *
   * The evaluation may fail for the following reasons:
   *
   * - {@code t} contains a quantifier.
   *
   * - the model {@code m} is partial, that is, it doesn't have a complete
   * interpretation for uninterpreted functions.
   * That is, the option <code>MODEL_PARTIAL=true</code> was used.
   *
   * - {@code t} is type incorrect.
   */
  static native boolean model_eval(
      long context, long model, long a1, boolean model_completion, PointerToLong a2);

  /**
   * Return the interpretation (i.e., assignment) of constant {@code a} in the
   * model {@code m}.
   * Return {@code NULL}, if the model does not assign an interpretation for
   * {@code a}.
   * That should be interpreted as: the value of {@code a} does not matter.
   *
   * <p>Precondition: {@code get_arity(c, f) == 0}
   *
   * @param context z3context
   * @param model z3model
   * @param funcDecl Z3_func_decl
   * @return
   *      0 if the value does not matter.
   *      Z3_ast otherwise.
   */
  static native long model_get_const_interp(long context, long model, long funcDecl);

  /**
   * Return the interpretation of the function {@code f} in the model
   * {@code m}.
   * Return {@code NULL}, if the model does not assign an interpretation for
   * {@code f}.
   * That should be interpreted as: the {@code f} does not matter.
   *
   * <p>Precondition: {@code get_arity(c, f) > 0}
   *
   * @param context Z3_context
   * @param model Z3_model
   * @param funcDecl Z3_func_decl
   * @return
   *    0 if the value does not matter.
   *    Z3_func_interp otherwise.
   */
  static native long model_get_func_interp(long context, long model, long funcDecl);

  /**
   * Return the number of constants assigned by the given model.
   *
   * @param context Z3_context
   * @param model Z3_model
   */
  static native int model_get_num_consts(long context, long model);

  /**
   * Return the i-th constant in the given model.
   *
   * <p>Precondition: {@code i < Z3_model_get_num_consts(c, m)}
   *
   * @param context Z3_context
   * @param model Z3_model
   * @return Z3_func_decl
   */
  static native long model_get_const_decl(long context, long model, int i);

  /**
   * Return the number of function interpretations in the given model.
   *
   * <p>A function interpretation is represented as a finite map and an 'else' value.
   * Each entry in the finite map represents the value of a function given a set
   * of arguments.
   * @param context Z3_context
   * @param model Z3_model
   */
  static native int model_get_num_funcs(long context, long model);

  /**
   * Return the declaration of the i-th function in the given model.
   *
   * <p>Precondition: {@code i < Z3_model_get_num_funcs(c, m)}
   *
   * @param context Z3_context
   * @param model Z3_model
   * @return Z3_func_decl
   */
  static native long model_get_func_decl(long context, long model, int i);

  /**
   * Return the number of uninterpreted sorts that {@code m}
   * assigns an interpretation to.
   *
   * <p>Z3 also provides an interpretation for uninterpreted sorts used in a formula.
   * The interpretation for a sort {@code s} is a finite set of distinct values.
   * We say this finite set is the "universe" of {@code s}.
   *
   * @param context Z3_context
   * @param model Z3_model
   */
  static native int model_get_num_sorts(long context, long model);

  /**
   * Return a uninterpreted sort that {@code m} assigns an interpretation.
   *
   * <p>{@code i < Z3_model_get_num_sorts(c, m)}
   *
   * @param context Z3_context
   * @param model Z3_model
   * @return Z3_sort
   */
  static native long model_get_sort(long context, long model, int i);

  /**
   * Return the finite set of distinct values that represent the interpretation
   * for sort {@code s}.
   *
   * @param context Z3_context
   * @param model Z3_model
   * @param sort Z3_sort
   * @return Z3_ast_vector
   */
  static native long model_get_sort_universe(long context, long model, long sort);

  static native boolean is_as_array(long context, long a1);

  static native long get_as_array_func_decl(long context, long a1);

  /**
   * Increment the reference counter of the given Z3_func_interp object.
   *
   * @param context Z3_context
   * @param a1 Z3_func_interp
   */
  static native void func_interp_inc_ref(long context, long a1);

  /**
   * Decrease the reference counter of the given Z3_func_interp object.
   *
   * @param context Z3_context
   * @param a1 Z3_func_interp
   */
  static native void func_interp_dec_ref(long context, long a1);

  /**
   * Return the number of entries in the given function interpretation.
   *
   * <p>A function interpretation is represented as a finite map and an 'else' value.
   * Each entry in the finite map represents the value of a function given a set of arguments.
   * This procedure returns the number of element in the finite map of {@code f}.
   *
   * @param context Z3_context
   * @param a1 Z3_func_interp
   */
  static native int func_interp_get_num_entries(long context, long a1);

  /**
   * Return a "point" of the given function interpretation. It represents the
   * value of {@code f} in a particular point.
   *
   * <p>Precondition: {@code i < func_interp_get_num_entries(c, f)}
   *
   * @param context Z3_context
   * @param a1 Z3_func_interp
   * @param a2 index
   * @return Z3_func_entry
   */
  static native long func_interp_get_entry(long context, long a1, int a2);

  /**
   * Return the 'else' value of the given function interpretation.
   *
   * <p>A function interpretation is represented as a finite map and an 'else' value.
   * This procedure returns the 'else' value.
   *
   * @param context Z3_context
   * @param a1 Z3_func_interp
   * @return Z3_ast
   */
  static native long func_interp_get_else(long context, long a1);

  /**
   * Return the arity (number of arguments) of the given function interpretation.
   *
   * @param context Z3_context
   * @param a1 Z3_ast
   */
  static native int func_interp_get_arity(long context, long a1);

  static native void func_entry_inc_ref(long context, long a1);

  static native void func_entry_dec_ref(long context, long a1);

  /**
   * Return the value of this point.
   *
   * <p>A Z3_func_entry object represents an element in the finite map used to encode
   * a function interpretation.
   *
   * @param context Z3_context
   * @param a1 Z3_func_entry
   * @return Z3_ast
   */
  static native long func_entry_get_value(long context, long a1);

  /**
   * Return the number of arguments in a Z3_func_entry object.
   *
   * @param context Z3_context
   * @param a1 Z3_func_entry
   */
  static native int func_entry_get_num_args(long context, long a1);

  /**
   * Return an argument of a Z3_func_entry object.
   *
   * @param context Z3_context
   * @param a1 Z3_func_entry
   * @param a2 index
   * @return Z3_ast
   */
  static native long func_entry_get_arg(long context, long a1, int a2);

  // INTERACTION LOGGING
  static native boolean open_log(String filename);

  static native void append_log(String s);

  static native void close_log();

  static native void toggle_warning_messages(boolean enabled);

  // STRING CONVERSION
  static native void set_ast_print_mode(long context, int mode);

  static native String ast_to_string(long context, long ast);

  static native String pattern_to_string(long context, long pattern);

  static native String sort_to_string(long context, long sort);

  static native String func_decl_to_string(long context, long func_decl);

  static native String model_to_string(long context, long model);

  static native String benchmark_to_smtlib_string(
      long context,
      String name,
      String logic,
      String status,
      String attributes,
      int len,
      long[] assumptions,
      long ast);

  // PARSER INTERFACE
  private static native long parse_smtlib2_string(
      long context,
      String str,
      int len1,
      long[] sort_symbols,
      long[] sorts,
      int len2,
      long[] decl_symbols,
      long[] decls);

  private static native long parse_smtlib2_file(
      long context,
      String filename,
      int len1,
      long[] sort_symbols,
      long[] sorts,
      int len2,
      long[] decl_symbols,
      long[] decls);

  private static native void parse_smtlib_string(
      long context,
      String str,
      int len1,
      long[] sort_symbols,
      long[] sorts,
      int len2,
      long[] decl_symbols,
      long[] decls);

  private static native void parse_smtlib_file(
      long context,
      String filename,
      int len1,
      long[] sort_symbols,
      long[] sorts,
      int len2,
      long[] decl_symbols,
      long[] decls);

  static long parse_smtlib2_string(
      long context,
      String str,
      long[] sort_symbols,
      long[] sorts,
      long[] decl_symbols,
      long[] decls) {
    return parse_smtlib2_string(
        context,
        str,
        sort_symbols.length,
        sort_symbols,
        sorts,
        decl_symbols.length,
        decl_symbols,
        decls);
  }

  static long parse_smtlib2_file(
      long context,
      String filename,
      long[] sort_symbols,
      long[] sorts,
      long[] decl_symbols,
      long[] decls) {
    return parse_smtlib2_file(
        context,
        filename,
        sort_symbols.length,
        sort_symbols,
        sorts,
        decl_symbols.length,
        decl_symbols,
        decls);
  }

  static void parse_smtlib_string(
      long context,
      String str,
      long[] sort_symbols,
      long[] sorts,
      long[] decl_symbols,
      long[] decls) {
    parse_smtlib_string(
        context,
        str,
        sort_symbols.length,
        sort_symbols,
        sorts,
        decl_symbols.length,
        decl_symbols,
        decls);
  }

  static void parse_smtlib_file(
      long context,
      String filename,
      long[] sort_symbols,
      long[] sorts,
      long[] decl_symbols,
      long[] decls) {
    parse_smtlib_string(
        context,
        filename,
        sort_symbols.length,
        sort_symbols,
        sorts,
        decl_symbols.length,
        decl_symbols,
        decls);
  }

  static native int get_smtlib_num_formulas(long context);

  static native long get_smtlib_formula(long context, int i);

  static native int get_smtlib_num_assumptions(long context);

  static native long get_smtlib_assumption(long context, int i);

  static native int get_smtlib_num_decls(long context);

  static native long get_smtlib_decl(long context, int i);

  static native int get_smtlib_num_sorts(long context);

  static native long get_smtlib_sort(long context, int i);

  static native String get_smtlib_error(long context);

  static native void setInternalErrorHandler(long ctx);

  static native int get_error_code(long context);

  static native void set_error(long context, int error_code);

  static native String get_error_msg(int error_code);

  static native String get_error_msg_ex(long context, int error_code);

  // MISC
  static native void get_version(
      PointerToInt major, PointerToInt minor, PointerToInt build, PointerToInt revision);

  /**
   * Enable tracing messages tagged as {@code tag}.
   *
   * <p>NOTE: Works only if Z3 is compiled in DEBUG mode. No-op otherwise.
   */
  static native void enable_trace(String tag);

  /**
   * Disable tracing messages tagged as {@code tag}.
   */
  static native void disable_trace(String tag);

  static native void reset_memory();

  // EXTERNAL
  // TODO do we need external functions?

  // FIXPOINT FACILITIES
  // TODO callbacks missing, do we need them?
  // TODO missing function: fp_init?
  static native long mk_fixedpoint(long context);

  static native void fixedpoint_inc_ref(long context, long a1);

  static native void fixedpoint_dec_ref(long context, long a1);

  static native void fixedpoint_add_rule(long context, long a1, long a2, long a3);

  static native void fixedpoint_add_fact(long context, long a1, long a2, int a3, int[] a4);

  static native void fixedpoint_assert(long context, long a1, long a2);

  static native int fixedpoint_query(long context, long a1, long a2);

  static native int fixedpoint_query_relations(long context, long a1, int a2, long[] a3);

  static native long fixedpoint_get_answer(long context, long a1);

  static native String fixedpoint_get_reason_unknown(long context, long a1);

  static native void fixedpoint_update_rule(long context, long a1, long a2, long a3);

  static native int fixedpoint_get_num_levels(long context, long a1, long a2);

  static native long fixedpoint_get_cover_delta(long context, long a1, int a2, long a3);

  static native void fixedpoint_add_cover(long context, long a1, int a2, long a3, long a4);

  static native long fixedpoint_get_statistics(long context, long a1);

  static native void fixedpoint_register_relation(long context, long a1, long a2);

  static native void fixedpoint_set_predicate_representation(
      long context, long a1, long a2, int a3, long[] a4);

  static native long fixedpoint_get_rules(long context, long a1);

  static native long fixedpoint_get_assertions(long context, long a1);

  static native void fixedpoint_set_params(long context, long a1, long a2);

  static native String fixedpoint_get_help(long context, long a1);

  static native long fixedpoint_get_param_descrs(long context, long a1);

  static native String fixedpoint_to_string(long context, long a1, int a2, long[] a3);

  static native long fixedpoint_from_string(long context, long a1, String a2);

  static native long fixedpoint_from_file(long context, long a1, String a2);

  static native void fixedpoint_push(long context, long a1);

  static native void fixedpoint_pop(long context, long a1);

  // AST VECTORS
  static native long mk_ast_vector(long context);

  static native void ast_vector_inc_ref(long context, long ast_vector);

  static native void ast_vector_dec_ref(long context, long ast_vector);

  static native int ast_vector_size(long context, long ast_vector);

  static native long ast_vector_get(long context, long ast_vector, int i);

  static native void ast_vector_set(long context, long ast_vector, int i, long ast);

  static native void ast_vector_resize(long context, long ast_vector, int num);

  static native void ast_vector_push(long context, long ast_vector, long ast);

  static native long ast_vector_translate(
      long context_source, long ast_vector, long context_target);

  static native String ast_vector_to_string(long context, long ast_vector);

  // AST MAPS
  static native long mk_ast_map(long context);

  static native void ast_map_inc_ref(long context, long ast_map);

  static native void ast_map_dec_ref(long context, long ast_map);

  static native boolean ast_map_contains(long context, long ast_map, long ast);

  static native long ast_map_find(long context, long ast_map, long ast);

  static native void ast_map_insert(long context, long ast_map, long ast_key, long ast_value);

  static native void ast_map_erase(long context, long ast_map, long ast_key);

  static native void ast_map_reset(long context, long ast_map);

  static native int ast_map_size(long context, long ast_map);

  static native long ast_map_keys(long context, long ast_map);

  static native String ast_map_to_string(long context, long ast_map);

  // GOALS
  /**
   * Create a goal (aka problem). A goal is essentially a set
   * of formulas, that can be solved and/or transformed using
   * tactics and solvers.
   *
   * <p>If {@code models == true}, then model generation is enabled for the new goal.
   *
   * <p>If {@code unsat_cores == true}, then unsat core generation is enabled for
   * the new goal.
   *
   * <p>If {@code proofs == true}, then proof generation is enabled for the new
   * goal. Remark, the Z3 context c must have been created with proof
   * generation support.
   *
   * <p>Reference counting must be used to manage goals, even when the Z3_context was
   * created using {@link #mk_context} instead of {@link #mk_context_rc}.
   */
  static native long mk_goal(long context, boolean models, boolean unsat_cores, boolean proofs);

  static native void goal_inc_ref(long context, long goal);

  static native void goal_dec_ref(long context, long goal);

  static native int goal_precision(long context, long goal);

  /**
   * Add a new formula {@code ast} to the given goal.
   * @param context Z3_context
   * @param goal Z3_goal
   * @param ast Z3_ast
   */
  static native void goal_assert(long context, long goal, long ast);

  static native boolean goal_inconsistent(long context, long goal);

  static native int goal_depth(long context, long goal);

  static native void goal_reset(long context, long goal);

  static native int goal_size(long context, long goal);

  /**
   * Return a formula from the given goal.
   * @param context Z3_context
   * @param goal Z3_goal
   * @param index Formula index. Should be smaller than {@link #goal_size}.
   * @return Z3_ast
   */
  static native long goal_formula(long context, long goal, int index);

  static native int goal_num_exprs(long context, long goal);

  static native boolean goal_is_decided_sat(long context, long goal);

  static native boolean goal_is_decided_unsat(long context, long goal);

  static native long goal_translate(long context_source, long goal, long context_target);

  static native String goal_to_string(long context, long goal);

  // TACTICS AND PROBES
  /**
   * Return a tactic associated with the given name.
   * The complete list of tactics may be obtained using the procedures
   * {@link #get_num_tactics} and {@link #get_tactic_name}.
   *
   * <p>Tactics are the basic building block for creating custom solvers for
   * specific problem domains.
   *
   * @param context Z3_context
   * @return Z3_tactic
   */
  static native long mk_tactic(long context, String name);

  static native void tactic_inc_ref(long context, long tactic);

  static native void tactic_dec_ref(long context, long tactic);

  static native long mk_probe(long context, String name);

  static native void probe_inc_ref(long context, long probe);

  static native void probe_dec_ref(long context, long probe);

  static native long tactic_and_then(long context, long tactic1, long tactic2);

  static native long tactic_or_else(long context, long tactic1, long tactic2);

  static native long tactic_par_or(long context, int len, long[] tactics);

  static native long tactic_par_and_then(long context, long tactic1, long tactic2);

  static native long tactic_try_for(long context, long tactic, int milliseconds);

  static native long tactic_when(long context, long probe, long tactic);

  static native long tactic_cond(long context, long probe, long tactic1, long tactic2);

  static native long tactic_repeat(long context, long tactic, int num_max);

  static native long tactic_skip(long context);

  static native long tactic_fail(long context);

  static native long tactic_fail_if(long context, long probe);

  static native long tactic_fail_if_not_decided(long context);

  static native long tactic_using_params(long context, long probe, long params);

  static native long probe_const(long context, double v);

  static native long probe_lt(long context, long probe1, long probe2);

  static native long probe_gt(long context, long probe1, long probe2);

  static native long probe_le(long context, long probe1, long probe2);

  static native long probe_ge(long context, long probe1, long probe2);

  static native long probe_eq(long context, long probe1, long probe2);

  static native long probe_and(long context, long probe1, long probe2);

  static native long probe_or(long context, long probe1, long probe2);

  static native long probe_not(long context, long probe1);

  static native int get_num_tactics(long context);

  static native String get_tactic_name(long context, int index);

  static native int get_num_probes(long context);

  static native String get_probe_name(long context, int index);

  static native String tactic_get_help(long context, long tactic);

  static native long tactic_get_param_descrs(long context, long tactic);

  static native String tactic_get_descr(long context, String name);

  static native String probe_get_descr(long context, String name);

  static native double probe_apply(long context, long probe, long goal);

  /**
   * Apply tactic {@code t} to the goal {@code goal}.
   *
   * @param context Z3_context
   * @param t Z3_tactic
   * @param goal Z3_goal
   * @return Z3_apply_result
   */
  static native long tactic_apply(long context, long t, long goal) throws InterruptedException;

  /**
   * Apply tactic {@code t} to the goal {@code goal} using the parameter set
   * {@code params}
   *
   * @param context Z3_context
   * @param tactic Z3_tactic
   * @param goal Z3_goal
   * @param params Z3_params
   * @return Z3_apply_result
   */
  static native long tactic_apply_ex(long context, long tactic, long goal, long params);

  static native void apply_result_inc_ref(long context, long apply_result);

  static native void apply_result_dec_ref(long context, long apply_result);

  static native String apply_result_to_string(long context, long apply_result);

  static native int apply_result_get_num_subgoals(long context, long apply_result);

  /**
   * Return one of the subgoals in the {@code Z3_apply_result} object returned
   * by {#link tactic_apply}.
   *
   * <p>Precondition: {@code i < apply_result_get_num_subgoals(c, r)}
   * @param context Z3_context
   * @param apply_result Z3_apply_result
   * @param i Apply result index
   * @return Z3_goal
   */
  static native long apply_result_get_subgoal(long context, long apply_result, int i);

  /**
   * Convert a model for the subgoal {@link #apply_result_get_subgoal}
   * for arguments {@code (c, r, i)}
   * into a model for the original goal {@code g}.
   * Where {@code g} is the goal used to create {@code r} using {@code tactic_apply(c, t, g)}
   * @param context Z3_context
   * @param apply_result Z3_apply_result
   * @param i index
   * @param model Z3_model
   * @return Z3_model
   */
  static native long apply_result_convert_model(long context, long apply_result, int i, long model);

  // SOLVERS
  static native long mk_solver(long context);

  static native long mk_simple_solver(long context);

  static native long mk_solver_for_logic(long context, long logic);

  static native long mk_solver_from_tactic(long context, long tactic);

  static native String solver_get_help(long context, long solver);

  static native long solver_get_param_descrs(long context, long solver);

  static native void solver_set_params(long context, long solver, long params);

  static native void solver_inc_ref(long context, long solver);

  static native void solver_dec_ref(long context, long solver);

  static native void solver_push(long context, long solver);

  static native void solver_pop(long context, long solver, int number);

  static native void solver_reset(long context, long solver);

  static native int solver_get_num_scopes(long context, long solver);

  static native void solver_assert(long context, long solver, long ast);

  static native void solver_assert_and_track(long context, long solver, long ast, long p);

  static native long solver_get_assertions(long context, long solver);

  static native int solver_check(long context, long solver) throws Z3SolverException;

  static native int solver_check_assumptions(
      long context, long solver, int len, long[] assumptions);

  static native long solver_get_model(long context, long solver);

  static native long solver_get_proof(long context, long solver);

  /**
   * Return the unsatisfiable core for the problem.
   *
   * @return Z3_ast_vector
   */
  static native long solver_get_unsat_core(long context, long solver);

  static native String solver_get_reason_unknown(long context, long solver);

  static native long solver_get_statistics(long context, long solver);

  static native String solver_to_string(long context, long solver);

  // STATISTICS
  static native String stats_to_string(long context, long stats);

  static native void stats_inc_ref(long context, long stats);

  static native void stats_dec_ref(long context, long stats);

  static native int stats_size(long context, long stats);

  static native String stats_get_key(long context, long stats, int i);

  static native boolean stats_is_uint(long context, long stats, int i);

  static native boolean stats_is_double(long context, long stats, int i);

  static native int stats_get_uint_value(long context, long stats, int i);

  static native double stats_get_double_value(long context, long stats, int i);

  static native String interpolation_profile(long context);

  /**
   * Interpolation API
   */

  /**
   * Create an AST node marking a formula position for interpolation.
   * The node {@code a} must have Boolean sort.
   * @param c Z3_context
   * @param a Z3_ast
   * @return Z3_ast
   */
  static native long mk_interpolant(long c, long a);

  /**
   * This function generates a Z3 context suitable for generation of
   * interpolants. Formulas can be generated as abstract syntax trees in
   * this context using the Z3 C API.
   *
   * <p>Interpolants are also generated as AST's in this context.
   *
   * <p>If cfg is non-null, it will be used as the base configuration
   * for the Z3 context. This makes it possible to set Z3 options
   * to be used during interpolation. This feature should be used
   * with some caution however, as it may be that certain Z3 options
   * are incompatible with interpolation.
   *
   * @param cfg Z3_config
   * @return Z3_context
   */
  static native long mk_interpolation_context(long cfg);

  /** Compute an interpolant from a refutation. This takes a proof of
   * "false" from a set of formulas C, and an interpolation
   * pattern. The pattern {@code pat} is a formula combining the formulas in C
   * using logical conjunction and the "interp" operator (see
   * {@link #mk_interpolant}. This interp operator is logically the identity
   * operator. It marks the sub-formulas of the pattern for which interpolants should
   * be computed. The interpolant is a map sigma from marked subformulas to
   * formulas, such that, for each marked subformula phi of pat (where phi sigma
   * is phi with sigma(psi) substituted for each subformula psi of phi such that
   * psi in dom(sigma)):
   *
   * <p>1) phi sigma implies sigma(phi), and
   *
   * <p>2) sigma(phi) is in the common uninterpreted vocabulary between
   * the formulas of C occurring in phi and those not occurring in
   * phi
   *
   * <p>and moreover pat sigma implies false. In the simplest case
   * an interpolant for the pattern "(and (interp A) B)" maps A
   * to an interpolant for A /\ B.
   *
   * <p>The return value is a vector of formulas representing sigma. The
   * vector contains sigma(phi) for each marked subformula of pat, in
   * pre-order traversal. // TODO documentation wrong? it is POST-ORDER traversal!
   * This means that subformulas of phi occur before phi
   * in the vector. Also, subformulas that occur multiply in pat will
   * occur multiply in the result vector.
   *
   * <p>In particular, calling this function on a pattern of the
   * form (interp ... (interp (and (interp A_1) A_2)) ... A_N) will
   * result in a sequence interpolant for A_1, A_2,... A_N.
   *
   * <p>Neglecting interp markers, the pattern must be a conjunction of
   * formulas in C, the set of premises of the proof. Otherwise an
   * error is flagged.
   *
   * <p>Any premises of the proof not present in the pattern are
   * treated as "background theory". Predicate and function symbols
   * occurring in the background theory are treated as interpreted and
   * thus always allowed in the interpolant.
   *
   * <p>Interpolant may not necessarily be computable from all
   * proofs. To be sure an interpolant can be computed, the proof
   * must be generated by an SMT solver for which interpolation is
   * supported, and the premises must be expressed using only
   * theories and operators for which interpolation is supported.
   *
   * <p>Currently, the only SMT solver that is supported is the legacy
   * SMT solver. Such a solver is available as the default solver in
   * #Z3_context objects produced by {@link #mk_interpolation_context}.
   * Currently, the theories supported are equality with
   * uninterpreted functions, linear integer arithmetic, and the
   * theory of arrays (in SMT-LIB terms, this is AUFLIA).
   * Quantifiers are allowed. Use of any other operators (including
   * "labels") may result in failure to compute an interpolant from a
   * proof.
   *
   * @param c Z3_context logical context.
   * @param pf Z3_ast a refutation from premises (assertions) C
   * @param pat Z3_ast an interpolation pattern over C
   * @param p Z3_params parameters
   * @return Z3_ast_vector
   */
  static native long get_interpolant(long c, long pf, long pat, long p);

  /** Compute an interpolant for an unsatisfiable conjunction of formulas.
   *
   * <p>This takes as an argument an interpolation pattern as in
   * {@link #get_interpolant}. This is a conjunction, some subformulas of
   * which are marked with the "interp" operator (see {@link #mk_interpolant}).
   *
   * <p>The conjunction is first checked for unsatisfiability. The result
   * of this check is returned in the out parameter "status". If the result
   * is unsat, an interpolant is computed from the refutation as in #Z3_get_interpolant
   * and returned as a vector of formulas. Otherwise the return value is
   * an empty formula.
   *
   * <p>See {@link #get_interpolant} for a discussion of supported theories.
   *
   * <p>The advantage of this function over {@link #get_interpolant} is that
   * it is not necessary to create a suitable SMT solver and generate
   * a proof. The disadvantage is that it is not possible to use the
   * solver incrementally.
   *
   * @param c Z3_context logical context.
   * @param pat Z3_ast an interpolation pattern
   * @param p Z3_params parameters for solver creation
   * @param model returns model if satisfiable
   *
   * @return status of SAT check
   **/
  static native int compute_interpolant(
      long c, long pat, long p, PointerToLong interp, PointerToLong model);
}
