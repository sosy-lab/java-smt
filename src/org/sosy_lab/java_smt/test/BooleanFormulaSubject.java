/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.test;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.truth.Fact.simpleFact;
import static com.google.common.truth.Truth.assert_;

import com.google.common.truth.FailureMetadata;
import com.google.common.truth.SimpleSubjectBuilder;
import com.google.common.truth.StandardSubjectBuilder;
import com.google.common.truth.Subject;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * {@link Subject} subclass for testing assertions about BooleanFormulas with Truth (allows to use
 * <code>assert_().about(...).that(formula).isUnsatisfiable()</code> etc.).
 *
 * <p>For a test use either {@link SolverBasedTest0#assertThatFormula(BooleanFormula)}, or use
 * {@link StandardSubjectBuilder#about(com.google.common.truth.Subject.Factory)} and set a solver
 * via the method {@link #booleanFormulasOf(SolverContext)}.
 */
@SuppressFBWarnings("EQ_DOESNT_OVERRIDE_EQUALS")
public class BooleanFormulaSubject extends Subject<BooleanFormulaSubject, BooleanFormula> {

  private final SolverContext context;

  private BooleanFormulaSubject(
      FailureMetadata pMetadata, BooleanFormula pFormula, SolverContext pMgr) {
    super(pMetadata, pFormula);
    context = checkNotNull(pMgr);
  }

  /**
   * Use this for checking assertions about BooleanFormulas (given the corresponding solver) with
   * Truth: <code>assert_().about(booleanFormulasOf(context)).that(formula).is...()</code>.
   */
  public static Subject.Factory<BooleanFormulaSubject, BooleanFormula> booleanFormulasOf(
      final SolverContext context) {
    return (metadata, formula) -> new BooleanFormulaSubject(metadata, formula, context);
  }

  /**
   * Use this for checking assertions about BooleanFormulas (given the corresponding solver) with
   * Truth: <code>assertUsing(context)).that(formula).is...()</code>.
   */
  public static SimpleSubjectBuilder<BooleanFormulaSubject, BooleanFormula> assertUsing(
      final SolverContext context) {
    return assert_().about(booleanFormulasOf(context));
  }

  private void checkIsUnsat(final BooleanFormula subject, final String verb, final Object expected)
      throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      prover.push(subject);
      if (prover.isUnsat()) {
        return; // success
      }

      // get model for failure message
      try (Model model = prover.getModel()) {
        failWithoutActual(
            simpleFact(
                String.format(
                    "Not true that %s %s <%s>. It has counterexample <%s>",
                    actualAsString(), verb, expected, model)));
      }
    }
  }

  /**
   * Check that the subject is unsatisfiable. Will show a model (satisfying assignment) on failure.
   */
  public void isUnsatisfiable() throws SolverException, InterruptedException {
    if (context.getFormulaManager().getBooleanFormulaManager().isTrue(actual())) {
      failWithoutActual(
          simpleFact(
              String.format(
                  "Not true that %s is <unsatisfiable>. It is <trivially satisfiable>.",
                  actualAsString())));
    }

    checkIsUnsat(actual(), "is", "unsatisfiable");
  }

  /** Check that the subject is satisfiable. Will show an unsat core on failure. */
  public void isSatisfiable() throws SolverException, InterruptedException {
    isSatisfiable(false);
  }

  /**
   * Check that the subject is satisfiable. Will show an unsat core on failure.
   *
   * @param generateModel whether we check model iteration.
   */
  @SuppressWarnings("unused")
  public void isSatisfiable(boolean generateModel) throws SolverException, InterruptedException {
    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (bmgr.isFalse(actual())) {
      failWithoutActual(
          simpleFact(
              String.format(
                  "Not true that %s is <satisfiable>. It <trivially unsatisfiable>.",
                  actualAsString())));
    }

    try (ProverEnvironment prover =
        generateModel
            ? context.newProverEnvironment(ProverOptions.GENERATE_MODELS)
            : context.newProverEnvironment()) {
      prover.push(actual());
      if (!prover.isUnsat()) {
        if (generateModel) {
          try (Model m = prover.getModel()) {
            for (ValueAssignment v : m) {
              // ignore, we just check iteration
            }
          }
          @SuppressWarnings("unused")
          List<ValueAssignment> lst = prover.getModelAssignments();
        }
        return; // success
      }
    }

    try (ProverEnvironment prover =
        context.newProverEnvironment(ProverOptions.GENERATE_UNSAT_CORE)) {
      // Try to report unsat core for failure message if the solver supports it.
      for (BooleanFormula part : bmgr.toConjunctionArgs(actual(), true)) {
        prover.push(part);
      }
      if (!prover.isUnsat()) {
        throw new AssertionError("repated satisfiability check returned different result");
      }
      final List<BooleanFormula> unsatCore = prover.getUnsatCore();
      if (unsatCore.isEmpty() || (unsatCore.size() == 1 && actual().equals(unsatCore.get(0)))) {
        // empty or trivial unsat core
        failWithoutActual(
            simpleFact(String.format("Not true that %s is <satisfiable>", actualAsString())));
      } else {
        failWithoutActual(
            simpleFact(
                String.format(
                    "Not true that %s is <satisfiable>. It has unsat core <%s>",
                    actualAsString(), unsatCore)));
      }
    } catch (UnsupportedOperationException ex) {

      // Otherwise just fail.
      failWithoutActual(
          simpleFact(String.format("Not true that %s is <satisfiable>", actualAsString())));
    }
  }

  /**
   * Check that the subject is tautological, i.e., always holds. This is equivalent to calling
   * {@link #isEquivalentTo(BooleanFormula)} with the formula {@code true}, but it checks
   * satisfiability of the subject and unsatisfiability of the negated subject in two steps to
   * improve error messages.
   */
  public void isTautological() throws SolverException, InterruptedException {
    isSatisfiable();
    checkIsUnsat(
        context.getFormulaManager().getBooleanFormulaManager().not(actual()), "is", "tautological");
  }

  /**
   * Check that the subject is equivalent to a given formula, i.e. {@code subject <=> expected}
   * always holds. Will show a counterexample on failure.
   */
  public void isEquivalentTo(final BooleanFormula expected)
      throws SolverException, InterruptedException {
    if (actual().equals(expected)) {
      return;
    }

    final BooleanFormula f =
        context.getFormulaManager().getBooleanFormulaManager().xor(actual(), expected);

    checkIsUnsat(f, "is equivalent to", expected);
  }

  public void isEquisatisfiableTo(BooleanFormula other)
      throws SolverException, InterruptedException {
    BooleanFormulaManager bfmgr = context.getFormulaManager().getBooleanFormulaManager();
    checkIsUnsat(bfmgr.and(actual(), bfmgr.not(other)), " is not equisatisfiable with ", other);
  }

  /**
   * Check that the subject implies a given formula, i.e. {@code subject => expected} always holds.
   * Will show a counterexample on failure.
   */
  public void implies(final BooleanFormula expected) throws SolverException, InterruptedException {
    if (actual().equals(expected)) {
      return;
    }

    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    final BooleanFormula implication = bmgr.or(bmgr.not(actual()), expected);

    checkIsUnsat(bmgr.not(implication), "implies", expected);
  }
}
