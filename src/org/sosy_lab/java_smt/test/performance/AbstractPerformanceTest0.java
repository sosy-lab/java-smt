// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.performance;

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.ArrayList;
import java.util.List;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

@RunWith(Parameterized.class)
public abstract class AbstractPerformanceTest0 extends SolverBasedTest0 {

  /** Note: This is not the real limit. Please see #getSymbolLimit() for further multipliers. */
  private static final int[] SYMBOL_LIMITS = {100, 1000, 10000};
  // private static final int[] SYMBOL_LIMITS = {100, 200, 500, 1000, 2000, 5000, 10000, 20000};

  protected static final int TIMEUT_IN_MS = 1000;

  // for debugging and testing, do not enable this flag in the official junit test.
  private static final boolean ENABLE_SAT_CHECK = false;

  @Parameters(name = "{0} with {1} symbols")
  public static List<Object[]> getAllCombinations() {
    ImmutableList.Builder<Object[]> combinations = ImmutableList.builder();
    for (Solvers solver : Solvers.values()) {
      for (int limit : SYMBOL_LIMITS) {
        combinations.add(new Object[] {solver, limit});
      }
    }
    return combinations.build();
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public int symbolLimit;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Ignore // partially redundant
  @Test(timeout = TIMEUT_IN_MS)
  public void pushConjunctionWithoutPopTest() throws InterruptedException, SolverException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push(bmgr.and(lst));
      if (isSatCheckEnabled()) {
        Truth.assertThat(pe.isUnsat()).isFalse();
      }
    } // pop on ProverEnvironment#close
    closeContext();
  }

  @Ignore // partially redundant
  @Test(timeout = TIMEUT_IN_MS)
  public void pushConjunctionWithPopTest() throws InterruptedException, SolverException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push(bmgr.and(lst));
      if (isSatCheckEnabled()) {
        Truth.assertThat(pe.isUnsat()).isFalse();
      }
      pe.pop();
    }
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void pushSeparatelyWithoutPopTest() throws InterruptedException, SolverException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (BooleanFormula f : lst) {
        pe.push(f);
      }
      if (isSatCheckEnabled()) {
        Truth.assertThat(pe.isUnsat()).isFalse();
      }
    } // pop on ProverEnvironment#close
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void pushSeparatelyWithSeparatePopTest() throws InterruptedException, SolverException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (BooleanFormula f : lst) {
        pe.push(f);
      }
      if (isSatCheckEnabled()) {
        Truth.assertThat(pe.isUnsat()).isFalse();
      }
      for (@SuppressWarnings("unused") BooleanFormula f : lst) {
        pe.pop();
      }
    }
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void pushSeparatelyWithSinglePopTest() throws InterruptedException, SolverException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      for (BooleanFormula f : lst) {
        pe.addConstraint(f);
      }
      if (isSatCheckEnabled()) {
        Truth.assertThat(pe.isUnsat()).isFalse();
      }
      pe.pop();
    }
    closeContext();
  }

  @Ignore // just for testing and debugging
  @Test(timeout = TIMEUT_IN_MS * 3)
  public void pushCombinationTest() throws InterruptedException {
    List<BooleanFormula> lst = createConstraints();
    try (ProverEnvironment pe = context.newProverEnvironment()) {

      // test 1
      pe.push(bmgr.and(lst));
      pe.pop();

      // test 2
      for (BooleanFormula f : lst) {
        pe.push(f);
      }
      for (@SuppressWarnings("unused") BooleanFormula f : lst) {
        pe.pop();
      }

      // test 3
      pe.push();
      for (BooleanFormula f : lst) {
        pe.addConstraint(f);
      }
      pe.pop();
    }
    closeContext();
  }

  // lets use some more test that are not inherited from the super-class.

  @Ignore
  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsWithoutPopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.push(createConstraint(i));
      }
    } // pop on ProverEnvironment#close
    closeContext();
  }

  @Ignore // partially redundant
  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsWithPopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.addConstraint(createConstraint(i));
      }
      pe.pop();
    }
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsSeperatelyWithoutPopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.push(createConstraint(i));
      }
    } // pop on ProverEnvironment#close
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsOnTopWithSeparatePopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.push();
      }
      pe.addConstraint(bmgr.and(createConstraints()));
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.pop();
      }
    }
    closeContext();
  }

  @Ignore
  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsSeparatelyWithSeparatePopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.push(createConstraint(i));
      }
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.pop();
      }
    }
    closeContext();
  }

  @Ignore
  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsOnTopWithoutPopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.push();
      }
      pe.addConstraint(bmgr.and(createConstraints()));
    }
    closeContext();
  }

  @Ignore
  @Test(timeout = TIMEUT_IN_MS)
  public void pushSymbolsSeparatelyWithSinglePopTest() throws InterruptedException {
    try (ProverEnvironment pe = context.newProverEnvironment()) {
      pe.push();
      for (int i = 0; i < getSymbolLimit(); i++) {
        pe.addConstraint(createConstraint(i));
      }
      pe.pop();
    }
    closeContext();
  }

  @Test(timeout = TIMEUT_IN_MS)
  public void createSymbolsAndCloseTest() {
    createConstraints();
    closeContext();
  }

  protected final void closeContext() {
    context.close();
    context = null;
  }

  final int getSymbolLimit() {
    int solverMultiplier = 1;
    // switch (solverToUse()) {
    // case YICES2:
    // solverMultiplier = 30; // some solvers are way faster than others.
    // break;
    // case BOOLECTOR:
    // case CVC4:
    // case MATHSAT5:
    // solverMultiplier = 20;
    // break;
    // case SMTINTERPOL:
    // case Z3: // might be better, but segfaults on larger sizes of the solver-stack.
    // solverMultiplier = 10;
    // break;
    // case PRINCESS:
    // solverMultiplier = 1;
    // break;
    // default:
    // throw new AssertionError("unexpected solver: " + solverToUse());
    // }
    return symbolLimit * solverMultiplier;
  }

  private boolean isSatCheckEnabled() {
    return ENABLE_SAT_CHECK; // && getSymbolLimit() < 10000;
  }

  protected List<BooleanFormula> createConstraints() {
    List<BooleanFormula> lst = new ArrayList<>(getSymbolLimit());
    for (int i = 0; i < getSymbolLimit(); i++) {
      lst.add(createConstraint(i));
    }
    return lst;
  }

  protected abstract BooleanFormula createConstraint(int i);
}
