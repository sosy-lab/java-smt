package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import com.google.common.truth.Truth;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
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
    long options = bitwuzlaJNI.bitwuzla_options_new();
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 1);
    // Cadical is always the default solver, but this shows how to set the option
    bitwuzlaJNI.bitwuzla_set_option_mode(
        options, BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(), "cadical");
    bitwuzla = bitwuzlaJNI.bitwuzla_new(options);
  }

  @After
  public void freeEnvironment() {
    bitwuzlaJNI.bitwuzla_delete(bitwuzla);
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
    long sortbv4 = bitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long sortbv8 = bitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    // Create function sort.
    long[] domain = {sortbv8, sortbv4};
    long sortfun = bitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, sortbv8);

    long x = bitwuzlaJNI.bitwuzla_mk_const(sortbv8, "x");
    long f = bitwuzlaJNI.bitwuzla_mk_const(sortfun, "f");

    long term =
        bitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(),
            f,
            x,
            bitwuzlaJNI.bitwuzla_mk_term1_indexed2(
                BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), x, 6, 3));

    long resultSort = bitwuzlaJNI.bitwuzla_term_get_sort(term);

    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_equal(sortbv8, resultSort));
  }

  @Test
  public void quickstartExample() {
    // Create bit-vector sorts of size 4 and 8.
    long sortbv4 = bitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long sortbv8 = bitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    // Create function sort.
    long[] domain = {sortbv8, sortbv4};
    long sortfun = bitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, sortbv8);
    // Create array sort.
    long sortarr = bitwuzlaJNI.bitwuzla_mk_array_sort(sortbv8, sortbv8);

    // Create two bit-vector constants of that sort.
    long x = bitwuzlaJNI.bitwuzla_mk_const(sortbv8, "x");
    long y = bitwuzlaJNI.bitwuzla_mk_const(sortbv8, "y");
    long f = bitwuzlaJNI.bitwuzla_mk_const(sortfun, "f");
    long a = bitwuzlaJNI.bitwuzla_mk_const(sortarr, "a");
    // Create bit-vector values one and two of the same sort.
    long one = bitwuzlaJNI.bitwuzla_mk_bv_one(sortbv8);
    long two = bitwuzlaJNI.bitwuzla_mk_bv_value_uint64(sortbv8, 2);

    // (bvsdiv x (_ bv2 8))
    long sdiv =
        bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_SDIV.swigValue(), x, two);
    // (bvashr y (_ bv1 8))
    long ashr =
        bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_ASHR.swigValue(), y, one);
    // ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    long sdive =
        bitwuzlaJNI.bitwuzla_mk_term1_indexed2(
            BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), sdiv, 3, 0);
    // ((_ extract 3 0) (bvashr x (_ bv1 8)))
    long ashre =
        bitwuzlaJNI.bitwuzla_mk_term1_indexed2(
            BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), ashr, 3, 0);

    // (assert
    //     (distinct
    //         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    //         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
    bitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_DISTINCT.swigValue(), sdive, ashre));

    // (assert (= (f x ((_ extract 6 3) x)) y))
    bitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            bitwuzlaJNI.bitwuzla_mk_term3(
                BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(),
                f,
                x,
                bitwuzlaJNI.bitwuzla_mk_term1_indexed2(
                    BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT.swigValue(), x, 6, 3)),
            y));

    // (assert (= (select a x) y))
    bitwuzlaJNI.bitwuzla_assert(
        bitwuzla,
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            bitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), a, x),
            y));

    // (check-sat)
    long result = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(result, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Print model in SMT-LIBv2 format.
    System.out.println("Model:");
    long[] decls = {x, y, f, a};

    System.out.println("(");
    for (int i = 0; i < 4; ++i) {
      long sort = bitwuzlaJNI.bitwuzla_term_get_sort(decls[i]);
      System.out.print("  (define-fun " + bitwuzlaJNI.bitwuzla_term_get_symbol(decls[i]) + " (");
      if (bitwuzlaJNI.bitwuzla_sort_is_fun(sort)) {
        long value = bitwuzlaJNI.bitwuzla_get_value(bitwuzla, decls[i]);
        long[] size = new long[1];
        long[] children = bitwuzlaJNI.bitwuzla_term_get_children(value, size);
        assertEquals(2, size[0]);
        int j = 0;
        while (bitwuzlaJNI.bitwuzla_term_get_kind(children[1])
            == BitwuzlaKind.BITWUZLA_KIND_LAMBDA.swigValue()) {
          assertTrue(bitwuzlaJNI.bitwuzla_term_is_var(children[0]));
          System.out.print(
              (j > 0 ? " " : "")
                  + bitwuzlaJNI.bitwuzla_term_to_string(children[0])
                  + " "
                  + bitwuzlaJNI.bitwuzla_sort_to_string(
                      bitwuzlaJNI.bitwuzla_term_get_sort(children[0]))
                  + " ");
          value = children[1];
          children = bitwuzlaJNI.bitwuzla_term_get_children(value, size);
          j += 1;
        }
        assertTrue(bitwuzlaJNI.bitwuzla_term_is_var(children[0]));
        System.out.print(
            (j > 0 ? " " : "")
                + bitwuzlaJNI.bitwuzla_term_to_string(children[0])
                + " "
                + bitwuzlaJNI.bitwuzla_sort_to_string(
                    bitwuzlaJNI.bitwuzla_term_get_sort(children[0]))
                + ") ");
        System.out.print(
            bitwuzlaJNI.bitwuzla_sort_to_string(bitwuzlaJNI.bitwuzla_sort_fun_get_codomain(sort))
                + " ");
        System.out.println(bitwuzlaJNI.bitwuzla_term_to_string(children[1]));
      } else {
        System.out.println(
            ") "
                + bitwuzlaJNI.bitwuzla_sort_to_string(sort)
                + " "
                + bitwuzlaJNI.bitwuzla_term_to_string(
                    bitwuzlaJNI.bitwuzla_get_value(bitwuzla, decls[i])));
      }
    }
    System.out.println(")");

    System.out.println();

    // Print value for x, y, f and a.
    // Note: The returned string of bitwuzlaJNI.bitwuzla_term_value_get_str is only valid
    //       until the next call to bitwuzlaJNI.bitwuzla_term_value_get_str
    // Both x and y are bit-vector terms and their value is a bit-vector
    // value that can be printed via bitwuzlaJNI.bitwuzla_term_value_get_str().
    System.out.println(
        "value of x: "
            + bitwuzlaJNI.bitwuzla_term_value_get_str(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, x)));
    System.out.println(
        "value of y: "
            + bitwuzlaJNI.bitwuzla_term_value_get_str(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, y)));
    System.out.println();

    // f and a, on the other hand, are a function and array term, respectively.
    // The value of these terms is not a value term: for f, it is a lambda term,
    // and the value of a is represented as a store term. Thus we cannot use
    // bitwuzlaJNI.bitwuzla_term_value_get_str(), but we can print the value of the terms
    // via bitwuzlaJNI.bitwuzla_term_to_string().
    System.out.println("to_string representation of value of f:");
    System.out.println(
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, f)));
    System.out.println("to_string representation of value of a:");
    System.out.println(
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, a)));
    System.out.println();

    // Note that the assignment string of bit-vector terms is given as the
    // pure assignment string, either in binary, hexadecimal or decimal format,
    // whereas bitwuzlaJNI.bitwuzla_term_to_string() prints the value in SMT-LIB2 format
    // (in binary number format).
    System.out.println(
        "to_string representation of value of x: "
            + bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, x)));
    System.out.println(
        "to_string representation of value of y: "
            + bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, y)));
    System.out.println();

    // Query value of bit-vector term that does not occur in the input formula
    long v =
        bitwuzlaJNI.bitwuzla_get_value(
            bitwuzla,
            bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_MUL.swigValue(), x, x));
    System.out.println(
        "value of v = x * x: "
            + bitwuzlaJNI.bitwuzla_term_value_get_str(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, v)));
  }

  @Test
  public void boolType() {
    long pBoolType = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_bool(pBoolType));
  }

  @Test
  public void isFalse() {
    long pBoolType = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    long var1 = bitwuzlaJNI.bitwuzla_mk_const(pBoolType, "var1");
    long var2 = bitwuzlaJNI.bitwuzla_mk_const(pBoolType, "var2");

    Truth.assertThat(bitwuzlaJNI.bitwuzla_term_is_false(var1)).isFalse();
    Truth.assertThat(bitwuzlaJNI.bitwuzla_term_is_true(var1)).isFalse();
    Truth.assertThat(bitwuzlaJNI.bitwuzla_term_is_false(var2)).isFalse();
    Truth.assertThat(bitwuzlaJNI.bitwuzla_term_is_true(var2)).isFalse();
  }

  @Test
  public void testBvModel() {
    long bvSort = bitwuzlaJNI.bitwuzla_mk_bv_sort(32);
    long a = bitwuzlaJNI.bitwuzla_mk_const(bvSort, "a");
    long one = bitwuzlaJNI.bitwuzla_mk_bv_one(bvSort);
    long two = bitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort, 2);

    // 1 + 2 = a
    long add =
        bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_ADD.swigValue(), one, two);
    long eq = bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);

    bitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(res, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String aString = bitwuzlaJNI.bitwuzla_term_to_string(a);
    assertEquals("a", aString);
    String aValue =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, a));
    // #b00000000000000000000000000000011 == 3
    assertEquals("#b00000000000000000000000000000011", aValue);
    assertEquals("#b00000000000000000000000000000001", bitwuzlaJNI.bitwuzla_term_to_string(one));
    assertEquals("#b00000000000000000000000000000010", bitwuzlaJNI.bitwuzla_term_to_string(two));
  }

  @Test
  public void testBvArrayModel() {
    long bvSort4 = bitwuzlaJNI.bitwuzla_mk_bv_sort(4);
    long bvSort8 = bitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long sortArr = bitwuzlaJNI.bitwuzla_mk_array_sort(bvSort4, bvSort8);

    long var = bitwuzlaJNI.bitwuzla_mk_const(bvSort8, "var");
    long eleven = bitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long zero = bitwuzlaJNI.bitwuzla_mk_bv_zero(bvSort4);
    long one = bitwuzlaJNI.bitwuzla_mk_bv_one(bvSort4);

    long arr = bitwuzlaJNI.bitwuzla_mk_const(sortArr, "arr");

    // Array arr = {11, var} AND arr[0] == arr[1] -> var == 11
    long arrW11At0 =
        bitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), arr, zero, eleven);
    long arrWVarAt1 =
        bitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE.swigValue(), arrW11At0, one, var);
    long eq =
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            bitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arrWVarAt1, one),
            bitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), arrWVarAt1, zero));

    bitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(res, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String varString = bitwuzlaJNI.bitwuzla_term_to_string(var);
    assertEquals("var", varString);
    String varValue =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, var));

    assertEquals("#b00001011", varValue);
    assertEquals(
        varValue,
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, eleven)));
    assertEquals("#b0001", bitwuzlaJNI.bitwuzla_term_to_string(one));
    assertEquals("#b0000", bitwuzlaJNI.bitwuzla_term_to_string(zero));

    // Getting the model of the array prints the SMTLIB2 representation
    String arrWVarAt1Value =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, arrWVarAt1));
    assertEquals(
        "(store (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #b00000000) #b0000 #b00001011)"
            + " #b0001 #b00001011)",
        arrWVarAt1Value);

    // We can access the children of the arrays
    long[] sizeArr = new long[1];
    // Array children are structured in the following way:
    // {starting array, index, value} in "we add value at index to array"
    // Just declared (empty) arrays return an empty array
    long[] children = bitwuzlaJNI.bitwuzla_term_get_children(arrWVarAt1, sizeArr);
    assertEquals(3, children.length);
    assertEquals(3, sizeArr[0]);
    assertEquals(arrW11At0, children[0]);
    assertEquals(one, children[1]);
    assertEquals(var, children[2]);
    long[] children2 = bitwuzlaJNI.bitwuzla_term_get_children(arrW11At0, sizeArr);
    assertEquals(3, children.length);
    assertEquals(3, sizeArr[0]);
    assertEquals(arr, children2[0]);
    assertEquals(zero, children2[1]);
    assertEquals(eleven, children2[2]);
    long[] children3 = bitwuzlaJNI.bitwuzla_term_get_children(arr, sizeArr);
    assertEquals(0, children3.length);
    assertEquals(0, sizeArr[0]);
  }

  @Test
  public void testUfModel() {
    long boolSort = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    long res = bitwuzlaJNI.bitwuzla_mk_const(boolSort, "res");
    long bvSort8 = bitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long arg1 = bitwuzlaJNI.bitwuzla_mk_const(bvSort8, "arg1");
    long arg2 = bitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long[] domain = {bvSort8, bvSort8};
    long sortFun = bitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, boolSort);

    long foo = bitwuzlaJNI.bitwuzla_mk_const(sortFun, "foo");
    long appliedFoo =
        bitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), foo, arg1, arg2);

    long eq =
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), appliedFoo, res);
    bitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long result = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(result, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String resString = bitwuzlaJNI.bitwuzla_term_to_string(res);
    assertEquals("res", resString);
    String resValue =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, res));

    // Bitwuzla seems to default to false and zero
    assertEquals("false", resValue);
    assertEquals(
        "#b00000000",
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, arg1)));
    assertEquals("#b00001011", bitwuzlaJNI.bitwuzla_term_to_string(arg2));

    // Children of the UF are ordered the following:
    // {function, arguments...}
    // Declaration is empty array
    long[] sizeArr = new long[1];
    long[] childrenAppliedFoo = bitwuzlaJNI.bitwuzla_term_get_children(appliedFoo, sizeArr);
    assertEquals(3, childrenAppliedFoo.length);
    assertEquals(3, sizeArr[0]);
    assertEquals(foo, childrenAppliedFoo[0]);
    assertEquals(arg1, childrenAppliedFoo[1]);
    assertEquals(arg2, childrenAppliedFoo[2]);
    long[] childrenFoo = bitwuzlaJNI.bitwuzla_term_get_children(foo, sizeArr);
    assertEquals(0, childrenFoo.length);
    assertEquals(0, sizeArr[0]);
  }

  @Test
  public void testBoolModel() {
    long boolSort = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    long x = bitwuzlaJNI.bitwuzla_mk_const(boolSort, "x");
    long t = bitwuzlaJNI.bitwuzla_mk_true();
    long f = bitwuzlaJNI.bitwuzla_mk_false();

    // (x AND true) OR false
    long and = bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), x, t);
    long or = bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), and, f);

    bitwuzlaJNI.bitwuzla_assert(bitwuzla, or);
    long res = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(res, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String xString = bitwuzlaJNI.bitwuzla_term_to_string(x);
    assertEquals("x", xString);
    String xValue =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, x));

    assertEquals("true", xValue);
    assertEquals("true", bitwuzlaJNI.bitwuzla_term_to_string(t));
    assertEquals("false", bitwuzlaJNI.bitwuzla_term_to_string(f));

    // Children of AND and OR
    long[] sizeArr = new long[1];
    long[] childrenOr = bitwuzlaJNI.bitwuzla_term_get_children(or, sizeArr);
    assertEquals(2, childrenOr.length);
    assertEquals(2, sizeArr[0]);
    assertEquals(and, childrenOr[0]);
    assertEquals(f, childrenOr[1]);

    assertEquals(BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(or));

    long[] childrenAnd = bitwuzlaJNI.bitwuzla_term_get_children(and, sizeArr);
    assertEquals(2, childrenOr.length);
    assertEquals(2, sizeArr[0]);
    assertEquals(x, childrenAnd[0]);
    assertEquals(t, childrenAnd[1]);

    assertEquals(
        BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(and));
  }

  @Test
  public void testFpModel() {
    long fpSort = bitwuzlaJNI.bitwuzla_mk_fp_sort(5, 11);
    long rm = bitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzlaJNI.BITWUZLA_RM_RNE_get());
    long a = bitwuzlaJNI.bitwuzla_mk_const(fpSort, "a");
    long one = bitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "1");
    long two = bitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "2");

    // 1 + 2 = a
    long add =
        bitwuzlaJNI.bitwuzla_mk_term3(BitwuzlaKind.BITWUZLA_KIND_FP_ADD.swigValue(), rm, two, one);
    long eq = bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);

    bitwuzlaJNI.bitwuzla_assert(bitwuzla, eq);
    long res = bitwuzlaJNI.bitwuzla_check_sat(bitwuzla);
    assertEquals(res, BitwuzlaResult.BITWUZLA_SAT.swigValue());

    // Get model value as String
    String aString = bitwuzlaJNI.bitwuzla_term_to_string(a);
    assertEquals("a", aString);
    String aValue =
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzla, a));

    assertEquals("(fp #b0 #b10000 #b1000000000)", aValue);
    assertEquals("(fp #b0 #b01111 #b0000000000)", bitwuzlaJNI.bitwuzla_term_to_string(one));
    assertEquals("(fp #b0 #b10000 #b0000000000)", bitwuzlaJNI.bitwuzla_term_to_string(two));
  }

  @Test
  public void testTypes() {
    // A constant (BITWUZLA_KIND_CONSTANT) is both, a variable and a constant value
    // However a value is also a BITWUZLA_KIND_VALUE, while a variable is not
    long fpSort = bitwuzlaJNI.bitwuzla_mk_fp_sort(5, 11);
    long rm = bitwuzlaJNI.bitwuzla_mk_rm_value(bitwuzlaJNI.BITWUZLA_RM_RNE_get());
    long a = bitwuzlaJNI.bitwuzla_mk_const(fpSort, "a");
    long one = bitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "1");
    long two = bitwuzlaJNI.bitwuzla_mk_fp_from_real(fpSort, rm, "2");

    long boolSort = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    long res = bitwuzlaJNI.bitwuzla_mk_const(boolSort, "res");
    long bvSort8 = bitwuzlaJNI.bitwuzla_mk_bv_sort(8);
    long arg1 = bitwuzlaJNI.bitwuzla_mk_const(bvSort8, "arg1");
    long arg2 = bitwuzlaJNI.bitwuzla_mk_bv_value_uint64(bvSort8, 11);
    long[] domain = {bvSort8, bvSort8};
    long sortFun = bitwuzlaJNI.bitwuzla_mk_fun_sort(2, domain, boolSort);

    // (applied) UFs have 1 + arity children, the UF decl (in this case foo), then the arguments
    // in order. Applied UFs are also no "fun", but can only be discerned by KIND
    // The decl has no children, but you can get domain and codomain with API calls
    long foo = bitwuzlaJNI.bitwuzla_mk_const(sortFun, "foo");
    long appliedFoo =
        bitwuzlaJNI.bitwuzla_mk_term3(
            BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), foo, arg1, arg2);
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_fun(appliedFoo));
    assertTrue(bitwuzlaJNI.bitwuzla_term_is_bool(appliedFoo));
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_bool(bitwuzlaJNI.bitwuzla_term_get_sort(appliedFoo)));
    assertEquals(null, bitwuzlaJNI.bitwuzla_term_get_symbol(appliedFoo));
    assertEquals("foo", bitwuzlaJNI.bitwuzla_term_get_symbol(foo));
    long[] appliedFooChildren = bitwuzlaJNI.bitwuzla_term_get_children(appliedFoo, new long[1]);
    assertEquals(foo, appliedFooChildren[0]);
    assertEquals(arg1, appliedFooChildren[1]);
    assertEquals(arg2, appliedFooChildren[2]);
    assertEquals(
        0, bitwuzlaJNI.bitwuzla_term_get_children(appliedFooChildren[0], new long[1]).length);
    assertEquals(
        BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(),
        bitwuzlaJNI.bitwuzla_term_get_kind(appliedFoo));
    assertEquals(
        BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(foo));

    long add =
        bitwuzlaJNI.bitwuzla_mk_term3(BitwuzlaKind.BITWUZLA_KIND_FP_ADD.swigValue(), rm, two, one);
    long eq = bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(), add, a);
    long neg = bitwuzlaJNI.bitwuzla_mk_term1(BitwuzlaKind.BITWUZLA_KIND_NOT.swigValue(), eq);

    /*
        System.out.println(Arrays.toString(bitwuzlaJNI.bitwuzla_term_get_children(add, new long[1])));
        System.out.println(bitwuzlaJNI.bitwuzla_kind_to_string(bitwuzlaJNI.bitwuzla_term_get_kind(add)));
        System.out.println(Arrays.toString(bitwuzlaJNI.bitwuzla_term_get_children(eq, new long[1])));
        System.out.println(bitwuzlaJNI.bitwuzla_kind_to_string(bitwuzlaJNI.bitwuzla_term_get_kind(eq)));
        System.out.println(Arrays.toString(bitwuzlaJNI.bitwuzla_term_get_children(neg, new long[1])));
        System.out.println(bitwuzlaJNI.bitwuzla_kind_to_string(bitwuzlaJNI.bitwuzla_term_get_kind(neg)));
    */

    // Non-UF functions consist of a KIND and arguments.
    // You can get the KIND w bitwuzla_term_get_kind() and the arguments in the correct order w
    // bitwuzla_term_get_children()
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_fun(appliedFoo));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_fun(add));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_fun(eq));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_fun(neg));

    assertTrue(bitwuzlaJNI.bitwuzla_term_is_rm(rm));

    long aSort = bitwuzlaJNI.bitwuzla_term_get_sort(a);
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_bv_value(a));
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_fp(aSort));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_const(aSort));
    assertTrue(bitwuzlaJNI.bitwuzla_term_is_fp(a));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_var(a));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_value(a));
    assertNotEquals(
        BitwuzlaKind.BITWUZLA_KIND_VALUE.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(a));
    assertNotEquals(
        BitwuzlaKind.BITWUZLA_KIND_VARIABLE.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(a));
    assertEquals(
        BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(a));

    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_fun(aSort));
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_fp(aSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_rm(aSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_bool(aSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_bv(aSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_array(aSort));

    assertEquals("a", bitwuzlaJNI.bitwuzla_term_to_string(a));

    long oneSort = bitwuzlaJNI.bitwuzla_term_get_sort(one);
    assertEquals(
        BitwuzlaKind.BITWUZLA_KIND_VALUE.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(one));
    assertNotEquals(
        BitwuzlaKind.BITWUZLA_KIND_VARIABLE.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(one));
    assertNotEquals(
        BitwuzlaKind.BITWUZLA_KIND_CONSTANT.swigValue(), bitwuzlaJNI.bitwuzla_term_get_kind(one));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_bv_value(one));
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_fp(oneSort));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_const(oneSort));
    assertTrue(bitwuzlaJNI.bitwuzla_term_is_fp(one));
    assertFalse(bitwuzlaJNI.bitwuzla_term_is_var(one));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_fun(oneSort));
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_fp(oneSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_rm(oneSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_bool(oneSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_bv(oneSort));
    assertFalse(bitwuzlaJNI.bitwuzla_sort_is_array(oneSort));

    assertEquals("(fp #b0 #b01111 #b0000000000)", bitwuzlaJNI.bitwuzla_term_to_string(one));
  }
}
