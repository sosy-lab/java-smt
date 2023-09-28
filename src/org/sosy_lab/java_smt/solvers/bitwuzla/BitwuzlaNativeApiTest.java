package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

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
    bitwuzla = bitwuzlaJNI.bitwuzla_new(options);
  }

  @After
  public void freeEnvironment() {
    NativeLibraries.loadLibrary("bitwuzlaJNI");
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
    // First, create a Bitwuzla options instance.
    long options = bitwuzlaJNI.bitwuzla_options_new();
    // Then, enable model generation.
    bitwuzlaJNI.bitwuzla_set_option(
        options, BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS.swigValue(), 1);
    // Now, for illustration purposes, we enable CaDiCaL as SAT solver
    // (CaDiCaL is already configured by default).
    // Note: This will silently fall back to one of the compiled in SAT solvers
    // if the selected solver is not compiled in.
    bitwuzlaJNI.bitwuzla_set_option_mode(
        options, BitwuzlaOption.BITWUZLA_OPT_SAT_SOLVER.swigValue(), "cadical");
    // Then, create a Bitwuzla instance.
    long bitwuzlaInstance = bitwuzlaJNI.bitwuzla_new(options);

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
    System.out.println("This is the result of x: " + x);
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
        bitwuzlaInstance,
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_DISTINCT.swigValue(), sdive, ashre));

    // (assert (= (f x ((_ extract 6 3) x)) y))
    bitwuzlaJNI.bitwuzla_assert(
        bitwuzlaInstance,
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
        bitwuzlaInstance,
        bitwuzlaJNI.bitwuzla_mk_term2(
            BitwuzlaKind.BITWUZLA_KIND_EQUAL.swigValue(),
            bitwuzlaJNI.bitwuzla_mk_term2(
                BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT.swigValue(), a, x),
            y));

    // (check-sat)
    long result = bitwuzlaJNI.bitwuzla_check_sat(bitwuzlaInstance);

    System.out.println("Expect: sat");
    System.out.println(
        "Bitwuzla: "
            + (result == BitwuzlaResult.BITWUZLA_SAT.swigValue()
                ? "sat"
                : (result == BitwuzlaResult.BITWUZLA_UNSAT.swigValue() ? "unsat" : "unknown")));

    // Print model in SMT-LIBv2 format.
    System.out.println("Model:");
    long[] decls = {x, y, f, a};

    System.out.println("(");
    for (int i = 0; i < 4; ++i) {
      long sort = bitwuzlaJNI.bitwuzla_term_get_sort(decls[i]);
      System.out.print("  (define-fun " + bitwuzlaJNI.bitwuzla_term_get_symbol(decls[i]) + " (");
      if (bitwuzlaJNI.bitwuzla_sort_is_fun(sort)) {
        long value = bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, decls[i]);
        long[] size = new long[1];
        long children = bitwuzlaJNI.bitwuzla_term_get_children(value, size);
        assertEquals(2, size[0]);
        int j = 0;
        while (bitwuzlaJNI.bitwuzla_term_get_kind(
                bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 1))
            == BitwuzlaKind.BITWUZLA_KIND_LAMBDA.swigValue()) {
          assertTrue(
              bitwuzlaJNI.bitwuzla_term_is_var(bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0)));
          System.out.print(
              (j > 0 ? " " : "")
                  + bitwuzlaJNI.bitwuzla_term_to_string(
                      bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0))
                  + " "
                  + bitwuzlaJNI.bitwuzla_sort_to_string(
                      bitwuzlaJNI.bitwuzla_term_get_sort(
                          bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0)))
                  + " ");
          value = bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 1);
          children = bitwuzlaJNI.bitwuzla_term_get_children(value, size);
          j += 1;
        }
        assertTrue(
            bitwuzlaJNI.bitwuzla_term_is_var(bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0)));
        System.out.print(
            (j > 0 ? " " : "")
                + bitwuzlaJNI.bitwuzla_term_to_string(
                    bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0))
                + " "
                + bitwuzlaJNI.bitwuzla_sort_to_string(
                    bitwuzlaJNI.bitwuzla_term_get_sort(
                        bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 0)))
                + ") ");
        System.out.print(
            bitwuzlaJNI.bitwuzla_sort_to_string(bitwuzlaJNI.bitwuzla_sort_fun_get_codomain(sort))
                + " ");
        System.out.println(
            bitwuzlaJNI.bitwuzla_term_to_string(
                bitwuzlaJNI.BitwuzlaTermArray_getitem(children, 1)));
      } else {
        System.out.println(
            ") "
                + bitwuzlaJNI.bitwuzla_sort_to_string(sort)
                + " "
                + bitwuzlaJNI.bitwuzla_term_to_string(
                    bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, decls[i])));
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
            + bitwuzlaJNI.bitwuzla_term_value_get_str(
                bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, x)));
    System.out.println(
        "value of y: "
            + bitwuzlaJNI.bitwuzla_term_value_get_str(
                bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, y)));
    System.out.println();

    // f and a, on the other hand, are a function and array term, respectively.
    // The value of these terms is not a value term: for f, it is a lambda term,
    // and the value of a is represented as a store term. Thus we cannot use
    // bitwuzlaJNI.bitwuzla_term_value_get_str(), but we can print the value of the terms
    // via bitwuzlaJNI.bitwuzla_term_to_string().
    System.out.println("to_string representation of value of f:");
    System.out.println(
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, f)));
    System.out.println("to_string representation of value of a:");
    System.out.println(
        bitwuzlaJNI.bitwuzla_term_to_string(bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, a)));
    System.out.println();

    // Note that the assignment string of bit-vector terms is given as the
    // pure assignment string, either in binary, hexadecimal or decimal format,
    // whereas bitwuzlaJNI.bitwuzla_term_to_string() prints the value in SMT-LIB2 format
    // (in binary number format).
    System.out.println(
        "to_string representation of value of x: "
            + bitwuzlaJNI.bitwuzla_term_to_string(
                bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, x)));
    System.out.println(
        "to_string representation of value of y: "
            + bitwuzlaJNI.bitwuzla_term_to_string(
                bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, y)));
    System.out.println();

    // Query value of bit-vector term that does not occur in the input formula
    long v =
        bitwuzlaJNI.bitwuzla_get_value(
            bitwuzlaInstance,
            bitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_BV_MUL.swigValue(), x, x));
    System.out.println(
        "value of v = x * x: "
            + bitwuzlaJNI.bitwuzla_term_value_get_str(
                bitwuzlaJNI.bitwuzla_get_value(bitwuzlaInstance, v)));

    bitwuzlaJNI.bitwuzla_delete(bitwuzlaInstance);
    bitwuzlaJNI.bitwuzla_options_delete(options);
  }
    @Test
  public void boolType() {
    long pBoolType = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    assertTrue(bitwuzlaJNI.bitwuzla_sort_is_bool(pBoolType));
  }

}
