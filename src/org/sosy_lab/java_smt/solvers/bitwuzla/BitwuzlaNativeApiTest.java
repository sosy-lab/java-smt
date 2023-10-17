// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.truth.Truth;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class BitwuzlaNativeApiTest {
  private long bitwuzla;

  @BeforeClass
  public static void load() {
    try {
      NativeLibraries.loadLibrary("bitwuzlaJNI");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Bitwuzla is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    long options = BitwuzlaJNI.bitwuzla_options_new();
    BitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_REWRITE_LEVEL.swigValue(), 0);
    BitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 1);
    // Cadical is always the default solver, but this shows how to set the option
    BitwuzlaJNI.bitwuzla_set_option_mode(
        options, BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(), "cadical");
    bitwuzla = BitwuzlaJNI.bitwuzla_new(options);
  }

  @After
  public void freeEnvironment() {
    BitwuzlaJNI.bitwuzla_delete(bitwuzla);
  }

  //  @Test
  //  public void functionWithNoArguments() {
  //    NativeLibraries.loadLibrary("bitwuzlaJNI");
  //    long bool_sort = bitwuzlaJNI.bitwuzla_mk_bool_sort();
  //    long a = bitwuzlaJNI.bitwuzla_mk_var(bool_sort, "a");
  //
  //    long noArgumentUF =
  //        bitwuzlaJNI.bitwuzla_mk_term1(
  //            BitwuzlaKind.BITWUZLA_KIND_LAMBDA.swigValue(), a);
  //  }

  @Test
  public void unsignedFunctions() {
    long sortbv4 = BitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long sortbv8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    // Create function sort.
    long[] domain = {sortbv8, sortbv4};
    long sortfun = BitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, sortbv8);

    long x = BitwuzlaJNI.bitwuzla_mk_const(sortbv8, "x");
    long f = BitwuzlaJNI.bitwuzla_mk_const(sortfun, "f");

    long term =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(),
            f,
            x,
            BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
                BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), x, 6, 3));

    long resultSort = BitwuzlaJNI.bitwuzla_term_get_sort(term);

    assertThat(BitwuzlaJNI.bitwuzla_sort_is_equal(sortbv8, resultSort)).isTrue();
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void quickstartExample() {
    // Create bit-vector sorts of size 4 and 8.
    long sortbv4 = BitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long sortbv8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    // Create function sort.
    long[] domain = {sortbv8, sortbv4};
    long sortfun = BitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, sortbv8);
    // Create array sort.
    long sortarr = BitwuzlaJNI.bitwuzla_mk_array_sort(sortbv8, sortbv8);

    // Create two bit-vector constants of that sort.
    long x = BitwuzlaJNI.bitwuzla_mk_const(sortbv8, "x");
    long y = BitwuzlaJNI.bitwuzla_mk_const(sortbv8, "y");
    long f = BitwuzlaJNI.bitwuzla_mk_const(sortfun, "f");
    long a = BitwuzlaJNI.bitwuzla_mk_const(sortarr, "a");
    // Create bit-vector values one and two of the same sort.
    long one = BitwuzlaJNI.bitwuzla_mk_bv_one(sortbv8);
    long two = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(sortbv8, 2);

    // (bvsdiv x (_ bv2 8))
    long sdiv =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_SDIV.swigValue(), x, two);
    // (bvashr y (_ bv1 8))
    long ashr =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_ASHR.swigValue(), y, one);
    // ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    long sdive =
        BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
            BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), sdiv, 3, 0);
    // ((_ extract 3 0) (bvashr x (_ bv1 8)))
    long ashre =
        BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
            BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), ashr, 3, 0);

    // (assert
    //     (distinct
    //         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    //         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
    BitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_DISTINCT.swigValue(), sdive, ashre));

    // (assert (= (f x ((_ extract 6 3) x)) y))
    BitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            BitwuzlaJNI.bitwuzla_mk_term3(
                BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(),
                f,
                x,
                BitwuzlaJNI.bitwuzla_mk_term1_indexed2(
                    BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), x, 6, 3)),
            y));

    // (assert (= (select a x) y))
    BitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            BitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), a, x),
            y));

    // (check-sat)
    long result = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(result).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Print model in SMT-LIBv2 format.
    // We call the API to check that the calls work, but don't assert them
    long[] decls = {x, y, f, a};

    // System.out.println("(");
    for (int i = 0; i < 4; ++i) {
      long sort = BitwuzlaJNI.bitwuzla_term_get_sort(decls[i]);
      // System.out.print("  (define-fun " + BitwuzlaJNI.bitwuzla_term_get_symbol(decls[i]) + " (");
      BitwuzlaJNI.bitwuzla_term_get_symbol(decls[i]);
      if (BitwuzlaJNI.bitwuzla_sort_is_fun(sort)) {
        long value = BitwuzlaJNI.bitwuzla_get_value(bitwuzla, decls[i]);
        long[] size = new long[1];
        long[] children = BitwuzlaJNI.bitwuzla_term_get_children(value, size);
        assertThat(size[0]).isEqualTo(2);
        // int j = 0;
        while (BitwuzlaJNI.bitwuzla_term_get_kind(children[1])
            == BitwuzlaKind.BITWUZLA_KIND_LAMBDA.swigValue()) {
          assertThat(BitwuzlaJNI.bitwuzla_term_is_var(children[0])).isTrue();
          BitwuzlaJNI.bitwuzla_term_to_string(children[0]);
          BitwuzlaJNI.bitwuzla_sort_to_string(BitwuzlaJNI.bitwuzla_term_get_sort(children[0]));
          /*System.out.print(
          (j > 0 ? " " : "")
              + BitwuzlaJNI.bitwuzla_term_to_string(children[0])
              + " "
              + BitwuzlaJNI.bitwuzla_sort_to_string(
                  BitwuzlaJNI.bitwuzla_term_get_sort(children[0]))
              + " ");*/
          value = children[1];
          children = BitwuzlaJNI.bitwuzla_term_get_children(value, size);
          // j += 1;
        }
        assertThat(BitwuzlaJNI.bitwuzla_term_is_var(children[0])).isTrue();
        BitwuzlaJNI.bitwuzla_term_to_string(children[0]);
        BitwuzlaJNI.bitwuzla_sort_to_string(BitwuzlaJNI.bitwuzla_term_get_sort(children[0]));
        /*
        System.out.print(
            (j > 0 ? " " : "")
                + BitwuzlaJNI.bitwuzla_term_to_string(children[0])
                + " "
                + BitwuzlaJNI.bitwuzla_sort_to_string(
                    BitwuzlaJNI.bitwuzla_term_get_sort(children[0]))
                + ") ");*/
        BitwuzlaJNI.bitwuzla_sort_to_string(BitwuzlaJNI.bitwuzla_sort_fun_get_codomain(sort));
        /*
        System.out.print(
            BitwuzlaJNI.bitwuzla_sort_to_string(BitwuzlaJNI.bitwuzla_sort_fun_get_codomain(sort))
                + " ");*/
        BitwuzlaJNI.bitwuzla_term_to_string(children[1]);
        /*
        System.out.println(BitwuzlaJNI.bitwuzla_term_to_string(children[1]));*/
      } else {
        BitwuzlaJNI.bitwuzla_sort_to_string(sort);
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, decls[i]));
        /*
        System.out.println(
            ") "
                + BitwuzlaJNI.bitwuzla_sort_to_string(sort)
                + " "
                + BitwuzlaJNI.bitwuzla_term_to_string(
                    BitwuzlaJNI.bitwuzla_get_value(bitwuzla, decls[i])));*/
      }
    }
    // System.out.println(")");

    // Print value for x, y, f and a.
    // Note: The returned string of bitwuzlaJNI.bitwuzla_term_value_get_str is only valid
    //       until the next call to bitwuzlaJNI.bitwuzla_term_value_get_str
    // Both x and y are bit-vector terms and their value is a bit-vector
    // value that can be printed via bitwuzlaJNI.bitwuzla_term_value_get_str().
    BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, x));
    BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, y));
    /*
    System.out.println(
        "value of x: "
            + BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, x)));
    System.out.println(
        "value of y: "
            + BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, y)));
            */

    // f and a, on the other hand, are a function and array term, respectively.
    // The value of these terms is not a value term: for f, it is a lambda term,
    // and the value of a is represented as a store term. Thus we cannot use
    // bitwuzlaJNI.bitwuzla_term_value_get_str(), but we can print the value of the terms
    // via bitwuzlaJNI.bitwuzla_term_to_string().
    // System.out.println("to_string representation of value of f:");

    BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, f));
    /*
    System.out.println(
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, f)));*/
    // System.out.println("to_string representation of value of a:");

    BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, a));
    /*
    System.out.println(
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, a)));*/

    // Note that the assignment string of bit-vector terms is given as the
    // pure assignment string, either in binary, hexadecimal or decimal format,
    // whereas bitwuzlaJNI.bitwuzla_term_to_string() prints the value in SMT-LIB2 format
    // (in binary number format).
    BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, x));
    /*
    System.out.println(
        "to_string representation of value of x: "
            + BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, x)));*/
    BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, y));
    /*
    System.out.println(
        "to_string representation of value of y: "
            + BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, y)));*/

    // Query value of bit-vector term that does not occur in the input formula
    long v =
        BitwuzlaJNI.bitwuzla_get_value(
            bitwuzla,
            BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_MUL.swigValue(), x, x));
    /*
    System.out.println(
        "value of v = x * x: "
            + BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, v)));
            */
    BitwuzlaJNI.bitwuzla_term_value_get_str(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, v));
  }

  @Test
  public void boolType() {
    long pBoolType = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bool(pBoolType)).isTrue();
  }

  @Test
  public void isFalse() {
    long pBoolType = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    long var1 = BitwuzlaJNI.bitwuzla_mk_const(pBoolType, "var1");
    long var2 = BitwuzlaJNI.bitwuzla_mk_const(pBoolType, "var2");

    Truth.assertThat(BitwuzlaJNI.bitwuzla_term_is_false(var1)).isFalse();
    Truth.assertThat(BitwuzlaJNI.bitwuzla_term_is_true(var1)).isFalse();
    Truth.assertThat(BitwuzlaJNI.bitwuzla_term_is_false(var2)).isFalse();
    Truth.assertThat(BitwuzlaJNI.bitwuzla_term_is_true(var2)).isFalse();
  }

  @Test
  public void testBvModel() {
    long bvSort = BitwuzlaJNI.bitwuzla_mk_bv_sort(32);
    long a = BitwuzlaJNI.bitwuzla_mk_const(bvSort, "a");
    long one = BitwuzlaJNI.bitwuzla_mk_bv_one(bvSort);
    long two = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort, 2);

    // 1 + 2 = a
    long add =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_ADD.swigValue(), one, two);
    long eq = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String aString = BitwuzlaJNI.bitwuzla_term_to_string(a);
    assertThat(aString).isEqualTo("a");
    String aValue =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, a));
    // #b00000000000000000000000000000011 == 3
    assertThat(aValue).isEqualTo("#b00000000000000000000000000000011");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(one))
        .isEqualTo("#b00000000000000000000000000000001");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(two))
        .isEqualTo("#b00000000000000000000000000000010");
  }

  @Test
  public void testBvArrayModelStore() {
    long bvSort4 = BitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long sortArr = BitwuzlaJNI.bitwuzla_mk_array_sort(bvSort4, bvSort8);

    long var = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "var");
    long eleven = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long zero = BitwuzlaJNI.bitwuzla_mk_bv_zero(bvSort4);
    long one = BitwuzlaJNI.bitwuzla_mk_bv_one(bvSort4);

    long arr = BitwuzlaJNI.bitwuzla_mk_const(sortArr, "arr");

    // Array arr = {11, var} AND arr[0] == arr[1] -> var == 11
    long arrW11At0 =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), arr, zero, eleven);
    long arrWVarAt1 =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), arrW11At0, one, var);
    long eq =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            BitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arrWVarAt1, one),
            BitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arrWVarAt1, zero));

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String varString = BitwuzlaJNI.bitwuzla_term_to_string(var);
    assertThat(varString).isEqualTo("var");
    String varValue =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, var));

    assertThat(varValue).isEqualTo("#b00001011");
    assertThat(
            BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, eleven)))
        .isEqualTo(varValue);
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(one)).isEqualTo("#b0001");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(zero)).isEqualTo("#b0000");

    assertThat(BitwuzlaJNI.bitwuzla_term_is_array(arrWVarAt1)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_array(arr)).isTrue();

    // Getting the model of the array prints the SMTLIB2 representation
    long valueArrWVarAt1 = BitwuzlaJNI.bitwuzla_get_value(bitwuzla, arrWVarAt1);
    // The value of an STORE expression is not really helpful, see string below
    String arrWVarAt1ValueString = BitwuzlaJNI.bitwuzla_term_to_string(valueArrWVarAt1);
    assertThat(arrWVarAt1ValueString)
        .isEqualTo(
            "(store (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #b00000000) #b0000"
                + " #b00001011) #b0001 #b00001011)");

    // We can access the children of the arrays
    long[] sizeArr = new long[1];
    // Array children are structured in the following way:
    // {starting array, index, value} in "we add value at index to array"
    // Just declared (empty) arrays return an empty array
    long[] children = BitwuzlaJNI.bitwuzla_term_get_children(arrWVarAt1, sizeArr);
    assertThat(children).hasLength(3);
    assertThat(sizeArr[0]).isEqualTo(3);
    assertThat(children[0]).isEqualTo(arrW11At0);
    assertThat(children[1]).isEqualTo(one);
    assertThat(children[2]).isEqualTo(var);
    long[] children2 = BitwuzlaJNI.bitwuzla_term_get_children(arrW11At0, sizeArr);
    assertThat(children).hasLength(3);
    assertThat(sizeArr[0]).isEqualTo(3);
    assertThat(children2[0]).isEqualTo(arr);
    assertThat(children2[1]).isEqualTo(zero);
    assertThat(children2[2]).isEqualTo(eleven);
    long[] children3 = BitwuzlaJNI.bitwuzla_term_get_children(arr, sizeArr);
    assertThat(children3).isEmpty();
    assertThat(sizeArr[0]).isEqualTo(0);
  }

  @Test
  public void testBvArrayModelSelect() {
    long bvSort4 = BitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long sortArr = BitwuzlaJNI.bitwuzla_mk_array_sort(bvSort4, bvSort8);

    long eleven = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long zero = BitwuzlaJNI.bitwuzla_mk_bv_zero(bvSort4);
    long one = BitwuzlaJNI.bitwuzla_mk_bv_one(bvSort4);

    long arr = BitwuzlaJNI.bitwuzla_mk_const(sortArr, "arr");

    // Array arr[0] == (store arr[1] 11))[1]
    long selectArrAtZero =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arr, zero);
    long arrWElevenAt1 =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), arr, one, eleven);
    long selectArrWElevenAtOne =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arrWElevenAt1, one);
    long eq =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), selectArrAtZero, selectArrWElevenAtOne);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    String arrAtZeroString = BitwuzlaJNI.bitwuzla_term_get_symbol(selectArrAtZero);
    assertThat(arrAtZeroString).isNull();
    // Get model value arr[0] as String
    String arrAtZeroValueString =
        BitwuzlaJNI.bitwuzla_term_value_get_str(
            BitwuzlaJNI.bitwuzla_get_value(bitwuzla, selectArrAtZero));
    // 00001011 == 11
    assertThat(arrAtZeroValueString).isEqualTo("00001011");

    // Arrays w 2 children are structured in the following way:
    // {starting array, index} in "we select index from array"
    // Just declared (empty) arrays return an empty children array
    long[] children = BitwuzlaJNI.bitwuzla_term_get_children(selectArrAtZero, new long[1]);
    assertThat(children).hasLength(2);
    assertThat(children[0]).isEqualTo(arr);
    String arrSymbol = BitwuzlaJNI.bitwuzla_term_get_symbol(children[0]);
    assertThat(arrSymbol).isEqualTo("arr");
    assertThat(children[1]).isEqualTo(zero);
  }

  @Test
  public void testUfModel() {
    long boolSort = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    long res = BitwuzlaJNI.bitwuzla_mk_const(boolSort, "res");
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long arg1 = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "arg1");
    long arg2 = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long[] domain = {bvSort8, bvSort8};
    long sortFun = BitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, boolSort);

    long foo = BitwuzlaJNI.bitwuzla_mk_const(sortFun, "foo");
    long appliedFoo =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), foo, arg1, arg2);

    long eq =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), appliedFoo, res);
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long result = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(result).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String resString = BitwuzlaJNI.bitwuzla_term_to_string(res);
    assertThat(resString).isEqualTo("res");
    String resValue =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, res));

    // Bitwuzla seems to default to false and zero
    assertThat(resValue).isEqualTo("false");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, arg1)))
        .isEqualTo("#b00000000");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(arg2)).isEqualTo("#b00001011");

    // Children of the UF are ordered the following:
    // {function, arguments...}
    // Declaration is empty array
    long[] sizeArr = new long[1];
    long[] childrenAppliedFoo = BitwuzlaJNI.bitwuzla_term_get_children(appliedFoo, sizeArr);
    assertThat(childrenAppliedFoo).hasLength(3);
    assertThat(sizeArr[0]).isEqualTo(3);
    assertThat(childrenAppliedFoo[0]).isEqualTo(foo);
    assertThat(childrenAppliedFoo[1]).isEqualTo(arg1);
    assertThat(childrenAppliedFoo[2]).isEqualTo(arg2);
    long[] childrenFoo = BitwuzlaJNI.bitwuzla_term_get_children(foo, sizeArr);
    assertThat(childrenFoo).isEmpty();
    assertThat(sizeArr[0]).isEqualTo(0);
  }

  @Test
  public void testBoolModel() {
    long boolSort = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    long x = BitwuzlaJNI.bitwuzla_mk_const(boolSort, "x");
    long t = BitwuzlaJNI.bitwuzla_mk_true();
    long f = BitwuzlaJNI.bitwuzla_mk_false();

    // (x AND true) OR false
    long and = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), x, t);
    long or = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), and, f);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, or);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String xString = BitwuzlaJNI.bitwuzla_term_to_string(x);
    assertThat(xString).isEqualTo("x");
    String xValue =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, x));

    assertThat(xValue).isEqualTo("true");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(t)).isEqualTo("true");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(f)).isEqualTo("false");

    // Children of AND and OR
    long[] sizeArr = new long[1];
    long[] childrenOr = BitwuzlaJNI.bitwuzla_term_get_children(or, sizeArr);
    assertThat(childrenOr).hasLength(2);
    assertThat(sizeArr[0]).isEqualTo(2);
    assertThat(childrenOr[0]).isEqualTo(and);
    assertThat(childrenOr[1]).isEqualTo(f);

    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(or))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_OR.swigValue());

    long[] childrenAnd = BitwuzlaJNI.bitwuzla_term_get_children(and, sizeArr);
    assertThat(childrenOr).hasLength(2);
    assertThat(sizeArr[0]).isEqualTo(2);
    assertThat(childrenAnd[0]).isEqualTo(x);
    assertThat(childrenAnd[1]).isEqualTo(t);

    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(and))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_AND.swigValue());
  }

  @Test
  public void testFpModel() {
    long fpSort = BitwuzlaJNI.bitwuzla_mk_fp_sort(5, 11);
    long rm = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RNE_get());
    long a = BitwuzlaJNI.bitwuzla_mk_const(fpSort, "a");
    long one = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "1");
    // Rational with 0 (or only 0s) as the second argument crashes Bitwuzla!
    long two = BitwuzlaJNI.bitwuzla_mk_fp_from_rational(fpSort, rm, "2", "1");

    // 1 + 2 = a
    long add =
        BitwuzlaJNI.bitwuzla_mk_term3(BitwuzlaKind.BITWUZLA_KIND_FP_ADD.swigValue(), rm, two, one);
    long eq = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String aString = BitwuzlaJNI.bitwuzla_term_to_string(a);
    assertThat(aString).isEqualTo("a");
    String aValue =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, a));

    assertThat(aValue).isEqualTo("(fp #b0 #b10000 #b1000000000)");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(one)).isEqualTo("(fp #b0 #b01111 #b0000000000)");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(two)).isEqualTo("(fp #b0 #b10000 #b0000000000)");
  }

  @Test
  public void testFpToBv() {
    // A constant (BITWUZLA_KIND_CONSTANT) is both, a variable and a constant value
    // However a value is also a BITWUZLA_KIND_VALUE, while a variable is not
    long fpSort = BitwuzlaJNI.bitwuzla_mk_fp_sort(5, 11);
    long rm = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RTZ_get());
    long a = BitwuzlaJNI.bitwuzla_mk_const(fpSort, "a");
    long one = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "-1");
    long two = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "2");

    long bvOne =
        BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV.swigValue(), rm, one, 11 + 5);
    long bvTwo =
        BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV.swigValue(), rm, two, 11 + 5);
    long add =
        BitwuzlaJNI.bitwuzla_mk_term3(BitwuzlaKind.BITWUZLA_KIND_FP_ADD.swigValue(), rm, two, one);
    long eq = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);

    long bvA =
        BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV.swigValue(), rm, a, 11 + 5);
    long bvAdd =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_ADD.swigValue(), bvOne, bvTwo);
    long eqBv =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), bvAdd, bvA);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eqBv);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    String bvAString =
        BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, bvA));

    assertThat(bvAString).isEqualTo("#b0000000000000001");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, bvOne)))
        .isEqualTo("#b1111111111111111");
    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(BitwuzlaJNI.bitwuzla_get_value(bitwuzla, bvTwo)))
        .isEqualTo("#b0000000000000010");
    // Now test -0.9 to 0 and 0.9 to 0
    long nearlyMin1 = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "-0.9");
    long nearly1 = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "0.9");
    long bvnearlyMin1 =
        BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV.swigValue(), rm, nearlyMin1, 11 + 5);
    long bvnearly1 =
        BitwuzlaJNI.bitwuzla_mk_term2_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV.swigValue(), rm, nearly1, 11 + 5);
    long b = BitwuzlaJNI.bitwuzla_mk_const(BitwuzlaJNI.bitwuzla_mk_bv_sort(11 + 5), "b");
    long bvAdd2 =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_BV_ADD.swigValue(), bvnearlyMin1, bvnearly1);
    long eqBv2 =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), bvAdd2, b);

    BitwuzlaJNI.bitwuzla_assert(bitwuzla, eqBv2);
    res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    assertThat(
            BitwuzlaJNI.bitwuzla_term_to_string(
                BitwuzlaJNI.bitwuzla_get_value(bitwuzla, bvnearlyMin1)))
        .isEqualTo("#b0000000000000000");
    assertThat(
            BitwuzlaJNI.bitwuzla_term_to_string(
                BitwuzlaJNI.bitwuzla_get_value(bitwuzla, bvnearly1)))
        .isEqualTo("#b0000000000000000");
  }

  @Test
  public void testTypes() {
    // A constant (BITWUZLA_KIND_CONSTANT) is both, a variable and a constant value
    // However a value is also a BITWUZLA_KIND_VALUE, while a variable is not
    long fpSort = BitwuzlaJNI.bitwuzla_mk_fp_sort(5, 11);
    long rm = BitwuzlaJNI.bitwuzla_mk_rm_value(BitwuzlaJNI.BITWUZLA_RM_RNE_get());
    long a = BitwuzlaJNI.bitwuzla_mk_const(fpSort, "a");
    long one = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "1");
    long two = BitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "2");

    long boolSort = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    //    long res = bitwuzlaJNI.bitwuzla_mk_const(boolSort, "res");
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long arg1 = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "arg1");
    long arg2 = BitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long[] domain = {bvSort8, bvSort8};
    long sortFun = BitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, boolSort);

    // (applied) UFs have 1 + arity children, the UF decl (in this case foo), then the arguments
    // in order. Applied UFs are also no "fun", but can only be discerned by KIND
    // The decl has no children, but you can get domain and codomain with API calls
    long foo = BitwuzlaJNI.bitwuzla_mk_const(sortFun, "foo");
    long appliedFoo =
        BitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), foo, arg1, arg2);
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(appliedFoo)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_bool(appliedFoo)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bool(BitwuzlaJNI.bitwuzla_term_get_sort(appliedFoo)))
        .isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_get_symbol(appliedFoo)).isNull();
    assertThat(BitwuzlaJNI.bitwuzla_term_get_symbol(foo)).isEqualTo("foo");
    assertThat(BitwuzlaJNI.bitwuzla_term_is_const(foo)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(foo)).isTrue();
    long[] appliedFooChildren = BitwuzlaJNI.bitwuzla_term_get_children(appliedFoo, new long[1]);
    assertThat(appliedFooChildren[0]).isEqualTo(foo);
    assertThat(appliedFooChildren[1]).isEqualTo(arg1);
    assertThat(appliedFooChildren[2]).isEqualTo(arg2);
    assertThat(BitwuzlaJNI.bitwuzla_term_get_children(appliedFooChildren[0], new long[1]))
        .isEmpty();
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(appliedFoo))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue());
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(foo))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue());

    long add =
        BitwuzlaJNI.bitwuzla_mk_term3(BitwuzlaKind.BITWUZLA_KIND_FP_ADD.swigValue(), rm, two, one);
    long eq = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);
    long neg = BitwuzlaJNI.bitwuzla_mk_term1(BitwuzlaKind.BITWUZLA_KIND_NOT.swigValue(), eq);

    // The type of add is fp (a bv add would be bv)
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fp(add)).isTrue();
    // eq is bool
    assertThat(BitwuzlaJNI.bitwuzla_term_is_bool(eq)).isTrue();
    // neg is also bool
    assertThat(BitwuzlaJNI.bitwuzla_term_is_bool(neg)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(neg)).isFalse();

    // Non-UF functions consist of a KIND and arguments.
    // You can get the KIND w bitwuzla_term_get_kind() and the arguments in the correct order w
    // bitwuzla_term_get_children()
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(appliedFoo)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(add)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(eq)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fun(neg)).isFalse();

    assertThat(BitwuzlaJNI.bitwuzla_term_is_rm(rm)).isTrue();

    long aSort = BitwuzlaJNI.bitwuzla_term_get_sort(a);
    assertThat(BitwuzlaJNI.bitwuzla_term_is_bv_value(a)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fp(aSort)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_const(aSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fp(a)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_var(a)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_value(a)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(a))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue());

    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fun(aSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fp(aSort)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_rm(aSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bool(aSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bv(aSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_array(aSort)).isFalse();

    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(a)).isEqualTo("a");

    long oneSort = BitwuzlaJNI.bitwuzla_term_get_sort(one);
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(one))
        .isEqualTo(BitwuzlaKind.BITWUZLA_KIND_VALUE.swigValue());
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(one))
        .isNotEqualTo(BitwuzlaKind.BITWUZLA_KIND_VARIABLE.swigValue());
    assertThat(BitwuzlaJNI.bitwuzla_term_get_kind(one))
        .isNotEqualTo(BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue());
    assertThat(BitwuzlaJNI.bitwuzla_term_is_bv_value(one)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fp(oneSort)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_const(oneSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_fp(one)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_term_is_var(one)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fun(oneSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_fp(oneSort)).isTrue();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_rm(oneSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bool(oneSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_bv(oneSort)).isFalse();
    assertThat(BitwuzlaJNI.bitwuzla_sort_is_array(oneSort)).isFalse();

    assertThat(BitwuzlaJNI.bitwuzla_term_to_string(one)).isEqualTo("(fp #b0 #b01111 #b0000000000)");
  }

  /*
   * This serves as a testbed for indexed terms
   */
  @Test
  public void testExtend() {
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long bvSort10 = BitwuzlaJNI.bitwuzla_mk_bv_sort(10);
    long x = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "x");
    long y = BitwuzlaJNI.bitwuzla_mk_const(bvSort10, "y");
    long xExt =
        BitwuzlaJNI.bitwuzla_mk_term1_indexed1(
            BitwuzlaKind.BITWUZLA_KIND_BV_SIGN_EXTEND.swigValue(), x, 2);
    long xExtEqY =
        BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), xExt, y);
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, xExtEqY);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_SAT.swigValue());

    long[] children = BitwuzlaJNI.bitwuzla_term_get_children(xExt, new long[1]);
    assertThat(children).hasLength(1);
    assertThat(BitwuzlaJNI.bitwuzla_term_is_indexed(xExt)).isTrue();
    long[] len = new long[1];
    long[] indices = BitwuzlaJNI.bitwuzla_term_get_indices(xExt, len);
    assertThat(indices).hasLength(1);
    assertThat(indices[0]).isEqualTo(2);
  }

  // Todo:
  @Ignore
  @Test
  public void testExists() {
    // EXISTS x, y . x = z AND y = z implies x = y
    long bvSort8 = BitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long x = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "x");
    long y = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "y");
    long z = BitwuzlaJNI.bitwuzla_mk_const(bvSort8, "z");

    long xEqZ = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), x, z);
    long yEqZ = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), y, z);
    long xEqY = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), x, y);
    long formula =
        BitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_IMPLIES.swigValue(),
            BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), xEqZ, yEqZ),
            xEqY);

    // Substitute the free vars with bound vars
    long xB = BitwuzlaJNI.bitwuzla_mk_var(bvSort8, "x");
    long yB = BitwuzlaJNI.bitwuzla_mk_var(bvSort8, "y");
    // Substitution does not return a new term, but modifies the existing!
    BitwuzlaJNI.bitwuzla_substitute_terms(
        1, new long[] {formula}, 2, new long[] {x, y}, new long[] {xB, yB});
    // Build quantifier
    long[] argsAndBody = {xB, yB, formula};
    long ex =
        BitwuzlaJNI.bitwuzla_mk_term(
            BitwuzlaKind.BITWUZLA_KIND_FORALL.swigValue(), argsAndBody.length, argsAndBody);

    // Check SAT
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, ex);
    long res = BitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertThat(res).isEqualTo(BitwuzlaResult.BITWUZLA_UNSAT.swigValue());

    // Model
  }

  @Test
  public void parserTest() {
    long boolSort = BitwuzlaJNI.bitwuzla_mk_bool_sort();
    long x = BitwuzlaJNI.bitwuzla_mk_const(boolSort, "x");
    long y = BitwuzlaJNI.bitwuzla_mk_const(boolSort, "y");
    long xOrY = BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), x, y);
    BitwuzlaJNI.bitwuzla_push(bitwuzla, 1);
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, xOrY);

    String dump = BitwuzlaJNI.dump_assertions_smt2(bitwuzla, 10);
    // check-sat and exit messes with the parse, in that suddenly sat is checked and the formulas
    // are rewritten and then returned in a different form, independent of options
    if (dump.contains("(check-sat)\n")) {
      dump = dump.replace("(check-sat)", "");
    }
    if (dump.contains("(exit)")) {
      dump = dump.replace("(exit)", "");
    }

    BitwuzlaJNI.bitwuzla_pop(bitwuzla, 1);

    long[] terms = BitwuzlaJNI.parse(dump);

    BitwuzlaJNI.bitwuzla_push(bitwuzla, 1);
    BitwuzlaJNI.bitwuzla_assert(bitwuzla, terms[0]);
    String newDump = BitwuzlaJNI.dump_assertions_smt2(bitwuzla, 10);
    if (newDump.contains("(check-sat)\n")) {
      newDump = newDump.replace("(check-sat)", "");
    }
    if (newDump.contains("(exit)")) {
      newDump = newDump.replace("(exit)", "");
    }
    assertThat(newDump).isEqualTo(dump);
  }

  @Ignore
  @Test
  public void parserFailTest() {
    // valid
    String input = "(declare-const a Bool)\n(declare-const b Bool)\n(assert (or a b))";
    long[] terms = BitwuzlaJNI.parse(input);
    assertThat(terms).isNotNull();
    // invalid/fails
    String badInput = "(declare-const a Bool)\n(assert (or a b))";
    terms = BitwuzlaJNI.parse(badInput);
    assertThat(terms).isNotNull();
  }
}
