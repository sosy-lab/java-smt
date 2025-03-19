/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Solver;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.sosy_lab.common.NativeLibraries;

@Ignore
public class CVC5ProofsTest {
  @BeforeClass
  public static void loadCVC5() {
    try {
      CVC5SolverContext.loadLibrary(NativeLibraries::loadLibrary);
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("CVC5 is not available", e);
    }
  }

  private Solver solver;

  @Before
  public void init() throws CVC5ApiException {
    solver = createEnvironment();
  }

  private static Solver createEnvironment() throws CVC5ApiException {
    Solver newSolver = new Solver();
    newSolver.setLogic("ALL");

    // options
    newSolver.setOption("incremental", "true");
    newSolver.setOption("produce-models", "true");
    newSolver.setOption("finite-model-find", "true");
    newSolver.setOption("sets-ext", "true");
    newSolver.setOption("output-language", "smtlib2");
    newSolver.setOption("strings-exp", "true");
    newSolver.setOption("produce-proofs", "true");

    return newSolver;
  }

}
