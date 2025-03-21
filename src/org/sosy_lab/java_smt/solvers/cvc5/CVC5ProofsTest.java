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

import static com.google.common.truth.Truth.assertThat;

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Proof;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
public class CVC5ProofsTest {

  @BeforeClass
  public static void loadCVC5() {
    try {
      CVC5SolverContext.loadLibrary(NativeLibraries::loadLibrary);
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("CVC5 is not available", e);
    }
  }

  private static TermManager tm;
  private static Sort booleanSort;
  private Solver solver;

  @Before
  public void init() throws CVC5ApiException {
    tm = new TermManager();
    booleanSort = tm.getBooleanSort();
    solver = createEnvironment();
  }

  private static Solver createEnvironment() throws CVC5ApiException {

    Solver newSolver = new Solver(tm);
    newSolver.setLogic("ALL");

    // options
    newSolver.setOption("incremental", "true");
    newSolver.setOption("produce-models", "true");
    newSolver.setOption("finite-model-find", "true");
    // newSolver.setOption("sets-ext", "true");
    newSolver.setOption("output-language", "smtlib2");
    newSolver.setOption("strings-exp", "true");
    newSolver.setOption("produce-proofs", "true");

    return newSolver;
  }

  private void processProof(Proof proof, int depth, int childNumber) throws CVC5ApiException {
    String indent = "  ".repeat(depth); // Indentation for readability

    System.out.println(indent + "Proof " + childNumber + ":");
    System.out.println(indent + "  Result: " + proof.getResult());
    System.out.println(indent + "  Rule: " + proof.getRule());
    System.out.println(indent + "  Num args: " + proof.getArguments().length);

    // Display arguments
    for (int j = 0; j < proof.getArguments().length; j++) {
      System.out.println(indent + "    Arg " + j + ": " + proof.getArguments()[j]);
    }

    Proof[] proofChildren = proof.getChildren();
    System.out.println(indent + "  Proof children length: " + proofChildren.length);

    for (int i = 0; i < proofChildren.length; i++) {
      System.out.println(indent + "  Child " + (i + 1) + " of Proof " + childNumber + ":");
      processProof(proofChildren[i], depth + 1, i + 1);
    }
  }

  @Test
  public void proofTest() throws CVC5ApiException {
    // (declare-fun q1 () Bool)
    // (declare-fun q2 () Bool)
    // (assert (or (not q1) q2))
    // (assert q1)
    // (assert (not q2))
    Sort booleanSort = tm.getBooleanSort();
    Term q1 = solver.declareFun("q1", new Sort[] {}, booleanSort);
    Term q2 = solver.declareFun("q2", new Sort[] {}, booleanSort);

    solver.assertFormula(tm.mkTerm(Kind.OR, (tm.mkTerm(Kind.NOT, q1)), q2));
    solver.assertFormula(q1);
    solver.assertFormula(tm.mkTerm(Kind.NOT, q2));

    assertThat(solver.checkSat().isUnsat()).isTrue();

    Proof[] proof = solver.getProof();

    System.out.println("Proof length: " + proof.length);

    // Process each proof in the array
    for (int i = 0; i < proof.length; i++) {
      processProof(proof[i], 0, i + 1);
    }
  }

  @Test
  public void cvc5ProofToStringTest() {
    // (declare-fun q1 () Bool)
    // (declare-fun q2 () Bool)
    // (assert (or (not q1) q2))
    // (assert q1)
    // (assert (not q2))
    Sort booleanSort = tm.getBooleanSort();
    Term q1 = solver.declareFun("q1", new Sort[] {}, booleanSort);
    Term q2 = solver.declareFun("q2", new Sort[] {}, booleanSort);

    solver.assertFormula(tm.mkTerm(Kind.OR, (tm.mkTerm(Kind.NOT, q1)), q2));
    solver.assertFormula(q1);
    solver.assertFormula(tm.mkTerm(Kind.NOT, q2));

    assertThat(solver.checkSat().isUnsat()).isTrue();

    Proof[] proof = solver.getProof();

    System.out.println("Proof length: " + proof.length);

    for (Proof p : proof) {
      System.out.println(solver.proofToString(p));
    }
  }
}
