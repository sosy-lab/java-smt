package org.sosy_lab.java_smt.solvers.bitwuzla;

import static org.junit.Assert.*;
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
      NativeLibraries.loadLibrary("bitwuzla");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Bitwuzla is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    NativeLibraries.loadLibrary("bitwuzla");
    bitwuzla = bitwuzlaJNI.bitwuzla_new();
  }

  @After
  public void freeEnvironment() {
    NativeLibraries.loadLibrary("bitwuzla");
    bitwuzlaJNI.bitwuzla_delete(bitwuzla);
  }

  @Test
  public void functionWithNoArguments() {
    NativeLibraries.loadLibrary("bitwuzla");
    long bool_sort = bitwuzlaJNI.bitwuzla_mk_bool_sort(bitwuzla);
    long a = bitwuzlaJNI.bitwuzla_mk_var(bitwuzla, bool_sort, "a");

    long noArgumentUF = bitwuzlaJNI.bitwuzla_mk_term1(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_LAMBDA.swigValue(), a);
  }
}
