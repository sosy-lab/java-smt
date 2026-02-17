// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static com.google.common.truth.Truth.assert_;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.Sets;
import com.google.common.truth.Fact;
import com.google.common.truth.FailureMetadata;
import com.google.common.truth.SimpleSubjectBuilder;
import com.google.common.truth.StandardSubjectBuilder;
import com.google.common.truth.Subject;
import com.google.common.truth.Truth;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * {@link Subject} subclass for testing assertions about BooleanFormulas with Truth (allows using
 * <code>assert_().about(...).that(formula).isUnsatisfiable()</code> etc.).
 *
 * <p>For a test use either {@link SolverBasedTest0#assertThatFormula(BooleanFormula)}, or use
 * {@link StandardSubjectBuilder#about(com.google.common.truth.Subject.Factory)} and set a solver
 * via the method {@link #booleanFormulasOf(SolverContext)}.
 */
public final class BooleanFormulaSubject extends Subject {

  private final SolverContext context;
  private final BooleanFormula formulaUnderTest;

  private BooleanFormulaSubject(
      FailureMetadata pMetadata, BooleanFormula pFormula, SolverContext pMgr) {
    super(pMetadata, pFormula);
    context = checkNotNull(pMgr);
    formulaUnderTest = checkNotNull(pFormula);
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
   * Use this for checking assertions about BooleanFormulas with Truth: <code>
   * assertThatFormula(formula).is...()</code>.
   */
  public static BooleanFormulaSubject assertThat(BooleanFormula formula, SolverContext context) {
    return assert_().about(booleanFormulasOf(context)).that(formula);
  }

  /**
   * Use this for checking assertions about BooleanFormulas (given the corresponding solver) with
   * Truth: <code>assertUsing(context)).that(formula).is...()</code>.
   */
  public static SimpleSubjectBuilder<BooleanFormulaSubject, BooleanFormula> assertUsing(
      final SolverContext context) {
    return assert_().about(booleanFormulasOf(context));
  }

  private void checkIsUnsat(
      final BooleanFormula subject, final Fact expected, ProverOptions... options)
      throws SolverException, InterruptedException {
    options =
        FluentIterable.of(ProverOptions.GENERATE_MODELS, options).toArray(ProverOptions.class);
    try (ProverEnvironment prover = context.newProverEnvironment(options)) {

      prover.push(subject);
      if (prover.isUnsat()) {
        return; // success
      }

      // get model for failure message
      try (Model model = prover.getModel()) {
        List<Fact> facts = new ArrayList<>();
        facts.add(Fact.fact("but was", formulaUnderTest));
        if (!subject.equals(formulaUnderTest)) {
          facts.add(Fact.fact("checked formula was", subject));
        }
        facts.add(Fact.fact("which has model", model));
        failWithoutActual(expected, facts.toArray(new Fact[0]));
      }
    }
  }

  /**
   * Check that the subject is unsatisfiable. Will show a model (satisfying assignment) on failure.
   */
  public void isUnsatisfiable(ProverOptions... options)
      throws SolverException, InterruptedException {
    if (context.getFormulaManager().getBooleanFormulaManager().isTrue(formulaUnderTest)) {
      failWithoutActual(
          Fact.fact("expected to be", "unsatisfiable"),
          Fact.fact("but was", "trivially satisfiable"));
      return;
    }

    checkIsUnsat(formulaUnderTest, Fact.simpleFact("expected to be unsatisfiable"), options);
  }

  /** Check that the subject is satisfiable. Will show an unsat core on failure. */
  public void isSatisfiable(ProverOptions... options) throws SolverException, InterruptedException {
    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (bmgr.isFalse(formulaUnderTest)) {
      failWithoutActual(
          Fact.fact("expected to be", "satisfiable"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }

    try (ProverEnvironment prover = context.newProverEnvironment(options)) {
      prover.push(formulaUnderTest);
      if (!prover.isUnsat()) {
        return; // success
      }
    }

    reportUnsatCoreForUnexpectedUnsatisfiableFormula(options);
  }

  /**
   * Check that the subject is satisfiable and provides a model for iteration.
   *
   * <p>Will show an unsat core on failure.
   */
  @SuppressWarnings({"unused", "resource"})
  void isSatisfiableAndHasModel(int maxSizeOfModel) throws SolverException, InterruptedException {
    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (bmgr.isFalse(formulaUnderTest)) {
      failWithoutActual(
          Fact.fact("expected to be", "satisfiable"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(formulaUnderTest);
      if (!prover.isUnsat()) {
        // check whether the model exists and we can iterate over it.
        // We allow an empty model, but it must be available.
        try (Model m = prover.getModel()) {
          for (ValueAssignment v : m) {
            // ignore, we just check iteration
          }
        }
        @SuppressWarnings("unused")
        List<ValueAssignment> lst = prover.getModelAssignments();
        Truth.assertThat(lst.size()).isAtMost(maxSizeOfModel);
        return; // success
      }
    }

    reportUnsatCoreForUnexpectedUnsatisfiableFormula();
  }

  private void reportUnsatCoreForUnexpectedUnsatisfiableFormula(ProverOptions... options)
      throws InterruptedException, SolverException, AssertionError {
    options =
        FluentIterable.of(ProverOptions.GENERATE_UNSAT_CORE, options).toArray(ProverOptions.class);
    try (ProverEnvironment prover = context.newProverEnvironment(options)) {
      // Try to report unsat core for failure message if the solver supports it.
      for (BooleanFormula part :
          context
              .getFormulaManager()
              .getBooleanFormulaManager()
              .toConjunctionArgs(formulaUnderTest, true)) {
        prover.push(part);
      }
      if (!prover.isUnsat()) {
        throw new AssertionError("repeated satisfiability check returned different result");
      }
      final List<BooleanFormula> unsatCore = prover.getUnsatCore();
      if (unsatCore.isEmpty()
          || (unsatCore.size() == 1 && formulaUnderTest.equals(unsatCore.get(0)))) {
        // empty or trivial unsat core
        failWithActual(Fact.fact("expected to be", "satisfiable"));
      } else {
        failWithoutActual(
            Fact.fact("expected to be", "satisfiable"),
            Fact.fact("but was", formulaUnderTest),
            Fact.fact("which has unsat core", Joiner.on('\n').join(unsatCore)));
      }
    } catch (UnsupportedOperationException ex) {

      // Otherwise just fail (unsat core not supported)
      failWithActual(Fact.fact("expected to be", "satisfiable"));
    }
  }

  /**
   * Check that the subject is tautological, i.e., always holds. This is equivalent to calling
   * {@link #isEquivalentTo(BooleanFormula)} with the formula {@code true}, but it checks
   * satisfiability of the subject and unsatisfiability of the negated subject in two steps to
   * improve error messages.
   */
  public void isTautological(ProverOptions... options)
      throws SolverException, InterruptedException {
    if (context.getFormulaManager().getBooleanFormulaManager().isFalse(formulaUnderTest)) {
      failWithoutActual(
          Fact.fact("expected to be", "tautological"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }
    checkIsUnsat(
        context.getFormulaManager().getBooleanFormulaManager().not(formulaUnderTest),
        Fact.fact("expected to be", "tautological"),
        options);
  }

  /**
   * Check that the subject is equivalent to a given formula, i.e. {@code subject <=> expected}
   * always holds. Will show a counterexample on failure.
   */
  public void isEquivalentTo(final BooleanFormula expected)
      throws SolverException, InterruptedException {
    if (formulaUnderTest.equals(expected)) {
      return;
    }

    final BooleanFormula f =
        context.getFormulaManager().getBooleanFormulaManager().xor(formulaUnderTest, expected);

    checkIsUnsat(f, Fact.fact("expected to be equivalent to", expected));
  }

  public void isEquisatisfiableTo(BooleanFormula other)
      throws SolverException, InterruptedException {
    BooleanFormulaManager bfmgr = context.getFormulaManager().getBooleanFormulaManager();
    checkIsUnsat(
        bfmgr.and(formulaUnderTest, bfmgr.not(other)),
        Fact.fact("expected to be equisatisfiable with", other));
  }

  /**
   * Check that the subject implies a given formula, i.e. {@code subject => expected} always holds.
   * Will show a counterexample on failure.
   */
  public void implies(final BooleanFormula expected) throws SolverException, InterruptedException {
    if (formulaUnderTest.equals(expected)) {
      return;
    }

    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    final BooleanFormula implication = bmgr.or(bmgr.not(formulaUnderTest), expected);

    checkIsUnsat(bmgr.not(implication), Fact.fact("expected to imply", expected));
  }

  /**
   * Checks if the subject is a valid Craig interpolant for the given formulas A and B.
   *
   * <p>Checks 3 properties:
   *
   * <ol>
   *   <li>I is a subset of A\B
   *   <li>A implies I
   *   <li>I and B are mutually contradictory
   * </ol>
   */
  public void isValidInterpolant(BooleanFormula formulaA, BooleanFormula formulaB)
      throws SolverException, InterruptedException {
    isValidInterpolant(List.of(formulaA), List.of(formulaB));
  }

  /** Checks if the subject is a valid Craig interpolant for the lists of formulas A and B. */
  public void isValidInterpolant(List<BooleanFormula> formulasA, List<BooleanFormula> formulasB)
      throws SolverException, InterruptedException {

    BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    BooleanFormula conjugatedFormulasOfA = bmgr.and(formulasA);
    BooleanFormula conjugatedFormulasOfB = bmgr.and(formulasB);

    // checks that every Symbol of the interpolant appears either in A or B
    FormulaManager mgr = context.getFormulaManager();
    Set<String> interpolantSymbols = mgr.extractVariablesAndUFs(formulaUnderTest).keySet();
    Set<String> interpolASymbols = mgr.extractVariablesAndUFs(conjugatedFormulasOfA).keySet();
    Set<String> interpolBSymbols = mgr.extractVariablesAndUFs(conjugatedFormulasOfB).keySet();
    Set<String> intersection = Sets.intersection(interpolASymbols, interpolBSymbols);

    checkState(
        intersection.containsAll(interpolantSymbols),
        "Interpolant contains symbols %s that are not part of both input formula groups A and B.",
        Sets.difference(interpolantSymbols, intersection));

    checkIsUnsat(
        bmgr.and(conjugatedFormulasOfA, bmgr.not(formulaUnderTest)),
        Fact.simpleFact("Interpolant expected to be implied by A (A => I)"),
        ProverOptions.GENERATE_MODELS);

    checkIsUnsat(
        bmgr.and(formulaUnderTest, conjugatedFormulasOfB),
        Fact.simpleFact("Interpolant expected to contradict B (I /\\ B => UNSAT)"),
        ProverOptions.GENERATE_MODELS);
  }
}
