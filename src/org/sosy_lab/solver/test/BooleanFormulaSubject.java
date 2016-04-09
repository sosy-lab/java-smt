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
package org.sosy_lab.solver.test;

import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.solver.api.SolverContext.ProverOptions.GENERATE_UNSAT_CORE;

import com.google.common.truth.FailureStrategy;
import com.google.common.truth.Subject;
import com.google.common.truth.SubjectFactory;
import com.google.common.truth.TestVerb;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;

import java.util.List;

/**
 * {@link Subject} subclass for testing assertions about BooleanFormulas with Truth
 * (allows to use <code>assert_().about(...).that(formula).isUnsatisfiable()</code> etc.).
 *
 * <p>Use {@link SolverBasedTest0#assertThatFormula(BooleanFormula)},
 * or {@link TestVerb#about(com.google.common.truth.SubjectFactory)} and
 * {@link #forSolver(SolverContext)}.
 */
@SuppressFBWarnings("EQ_DOESNT_OVERRIDE_EQUALS")
public class BooleanFormulaSubject extends Subject<BooleanFormulaSubject, BooleanFormula> {

  private final SolverContext context;

  private BooleanFormulaSubject(
      FailureStrategy pFailureStrategy, BooleanFormula pFormula, SolverContext pMgr) {
    super(pFailureStrategy, pFormula);
    context = checkNotNull(pMgr);
  }

  /**
   * Use this for checking assertions about BooleanFormulas
   * (given the corresponding solver) with Truth:
   * <code>assert_().about(BooleanFormulaSubject.forSolver(mgr)).that(formula).is...()</code>.
   */
  public static SubjectFactory<BooleanFormulaSubject, BooleanFormula> forSolver(
      final SolverContext context) {
    return new SubjectFactory<BooleanFormulaSubject, BooleanFormula>() {
      @Override
      public BooleanFormulaSubject getSubject(FailureStrategy pFs, BooleanFormula pFormula) {
        return new BooleanFormulaSubject(pFs, pFormula, context);
      }
    };
  }

  private void checkIsUnsat(final BooleanFormula subject, final String verb, final Object expected)
      throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      prover.push(subject);
      if (prover.isUnsat()) {
        return; // success
      }

      // get model for failure message
      try (final Model model = prover.getModel()) {
        failWithBadResults(verb, expected, "has counterexample", model);
      }
    }
  }

  /**
   * Check that the subject is unsatisfiable.
   * Will show a model (satisfying assignment) on failure.
   */
  public void isUnsatisfiable() throws SolverException, InterruptedException {
    if (context.getFormulaManager().getBooleanFormulaManager().isTrue(getSubject())) {
      failWithBadResults("is", "unsatisfiable", "is", "trivially satisfiable");
    }

    checkIsUnsat(getSubject(), "is", "unsatisfiable");
  }

  /**
   * Check that the subject is satisfiable.
   * Will show an unsat core on failure.
   */
  public void isSatisfiable() throws SolverException, InterruptedException {
    if (context.getFormulaManager().getBooleanFormulaManager().isFalse(getSubject())) {
      failWithBadResults("is", "satisfiable", "is", "trivially unsatisfiable");
    }

    try (ProverEnvironment prover = context.newProverEnvironment(GENERATE_UNSAT_CORE)) {
      prover.push(getSubject());
      if (!prover.isUnsat()) {
        return; // success
      }

      // get unsat core for failure message
      final List<BooleanFormula> unsatCore = prover.getUnsatCore();
      if (unsatCore.isEmpty() || (unsatCore.size() == 1 && getSubject().equals(unsatCore.get(0)))) {
        // empty or trivial unsat core
        fail("is", "satisfiable");
      } else {
        failWithBadResults("is", "satisfiable", "has unsat core", unsatCore);
      }
    }
  }

  /**
   * Check that the subject is tautological, i.e., always holds.
   * This is equivalent to calling {@link #isEquivalentTo(BooleanFormula)}
   * with the formula {@code true}, but it checks satisfiability of the subject
   * and unsatisfiability of the negated subject in two steps to improve error messages.
   */
  public void isTautological() throws SolverException, InterruptedException {
    isSatisfiable();
    checkIsUnsat(
        context.getFormulaManager().getBooleanFormulaManager().not(getSubject()),
        "is",
        "tautological");
  }

  /**
   * Check that the subject is equivalent to a given formula,
   * i.e. {@code subject <=> expected} always holds.
   * Will show a counterexample on failure.
   */
  public void isEquivalentTo(final BooleanFormula expected)
      throws SolverException, InterruptedException {
    if (getSubject().equals(expected)) {
      return;
    }

    final BooleanFormula f =
        context.getFormulaManager().getBooleanFormulaManager().xor(getSubject(), expected);

    checkIsUnsat(f, "is equivalent to", expected);
  }

  /**
   * Check that the subject implies a given formula,
   * i.e. {@code subject => expected} always holds.
   * Will show a counterexample on failure.
   */
  public void implies(final BooleanFormula expected) throws SolverException, InterruptedException {
    if (getSubject().equals(expected)) {
      return;
    }

    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    final BooleanFormula implication = bmgr.or(bmgr.not(getSubject()), expected);

    checkIsUnsat(bmgr.not(implication), "implies", expected);
  }
}
