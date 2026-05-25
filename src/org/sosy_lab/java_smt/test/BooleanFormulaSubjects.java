// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.truth.Truth.assert_;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.HashMultiset;
import com.google.common.collect.ImmutableList;
import com.google.common.truth.Fact;
import com.google.common.truth.FailureMetadata;
import com.google.common.truth.SimpleSubjectBuilder;
import com.google.common.truth.StandardSubjectBuilder;
import com.google.common.truth.Subject;
import com.google.common.truth.Truth;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * {@link Subject} subclass for testing assertions about BooleanFormulas with Truth (allows using
 * <code>assert_().about(...).that(formulas).areUnsatisfiable()</code> etc.).
 *
 * <p>For a test use either {@link SolverBasedTest0#assertThatFormulas(Collection)}, {@link
 * SolverBasedTest0#assertThatFormulas(BooleanFormula, BooleanFormula)} etc. , or use {@link
 * StandardSubjectBuilder#about(Factory)} and set a solver via the method {@link
 * #booleanFormulasOf(SolverContext)}.
 */
public final class BooleanFormulaSubjects extends Subject {

  private final SolverContext context;
  private final Collection<BooleanFormula> formulasUnderTest;

  private BooleanFormulaSubjects(
      FailureMetadata pMetadata, Collection<BooleanFormula> pFormulas, SolverContext pMgr) {
    super(pMetadata, pFormulas);
    context = checkNotNull(pMgr);
    formulasUnderTest = checkNotNull(pFormulas);
  }

  /**
   * Use this for checking assertions about {@link java.util.Collections} of {@link BooleanFormula}
   * s (given the corresponding solver) with Truth: <code>
   * assert_().about(booleanFormulasOf(context)).that(formula).is...()</code>.
   */
  public static Factory<BooleanFormulaSubjects, Collection<BooleanFormula>> booleanFormulasOf(
      final SolverContext context) {
    return (metadata, formulas) -> new BooleanFormulaSubjects(metadata, formulas, context);
  }

  /**
   * Use this for checking assertions about {@link java.util.Collections} of {@link BooleanFormula}
   * s (given the corresponding solver) with Truth: <code>
   * assertUsing(context)).that(formulas).are...()</code>.
   */
  public static SimpleSubjectBuilder<BooleanFormulaSubjects, Collection<BooleanFormula>>
      assertUsing(final SolverContext context) {
    return assert_().about(booleanFormulasOf(context));
  }

  private void checkIsUnsat(
      final Collection<BooleanFormula> subjects, final Fact expected, ProverOptions... options)
      throws SolverException, InterruptedException {
    options =
        FluentIterable.of(ProverOptions.GENERATE_MODELS, options).toArray(ProverOptions.class);
    try (ProverEnvironment prover = context.newProverEnvironment(options)) {

      for (BooleanFormula subject : subjects) {
        prover.push(subject);
      }

      if (prover.isUnsat()) {
        return; // success
      }

      // get model for failure message
      try (Model model = prover.getModel()) {
        List<Fact> facts = new ArrayList<>();
        facts.add(Fact.fact("but was", formulasUnderTest));
        if (!subjects.containsAll(formulasUnderTest)) {
          facts.add(Fact.fact("checked formulas were", subjects));
        }
        facts.add(Fact.fact("which have model", model));
        failWithoutActual(expected, facts.toArray(new Fact[0]));
      }
    }
  }

  /**
   * Check that the subjects is unsatisfiable by adding all to the solver stack individually and
   * checking satisfiability. This is in general equivalent to checking the conjunction of subjects
   * for satisfiability, but some solvers resolve individually asserted formulas distinctly to the
   * assertion of a conjunction of formulas. This is important for example in HORN solving. Will
   * show a model (satisfying assignment) on failure.
   */
  public void isUnsatisfiable(ProverOptions... options)
      throws SolverException, InterruptedException {
    if (formulasUnderTest.stream()
        .allMatch(f -> context.getFormulaManager().getBooleanFormulaManager().isTrue(f))) {
      failWithoutActual(
          Fact.fact("expected to be", "unsatisfiable"),
          Fact.fact("but was", "trivially satisfiable"));
      return;
    }

    checkIsUnsat(formulasUnderTest, Fact.simpleFact("expected to be unsatisfiable"), options);
  }

  /**
   * Check that the subjects are satisfiable by adding all to the solver stack individually and
   * checking satisfiability. This is in general equivalent to checking the conjunction of subjects
   * for satisfiability, but some solvers resolve individually asserted formulas distinctly to the
   * assertion of a conjunction of formulas. This is important for example in HORN solving. Will
   * show an unsat core on failure.
   */
  public void isSatisfiable(ProverOptions... options) throws SolverException, InterruptedException {
    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (formulasUnderTest.stream().allMatch(bmgr::isFalse)) {
      failWithoutActual(
          Fact.fact("expected to be", "satisfiable"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }

    try (ProverEnvironment prover = context.newProverEnvironment(options)) {
      for (BooleanFormula formula : formulasUnderTest) {
        prover.push(formula);
      }
      if (!prover.isUnsat()) {
        return; // success
      }
    }

    reportUnsatCoreForUnexpectedUnsatisfiableFormulas(options);
  }

  /**
   * Check that the conjunction of subjects is satisfiable and provides a model for iteration.
   *
   * <p>Will show an unsat core on failure.
   */
  @SuppressWarnings({"unused", "resource"})
  void isSatisfiableAndHaveModel(int maxSizeOfModel) throws SolverException, InterruptedException {
    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (formulasUnderTest.stream().allMatch(bmgr::isFalse)) {
      failWithoutActual(
          Fact.fact("expected to be", "satisfiable"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      for (BooleanFormula formula : formulasUnderTest) {
        prover.push(formula);
      }
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

    reportUnsatCoreForUnexpectedUnsatisfiableFormulas();
  }

  private void reportUnsatCoreForUnexpectedUnsatisfiableFormulas(ProverOptions... options)
      throws InterruptedException, SolverException, AssertionError {
    options =
        FluentIterable.of(ProverOptions.GENERATE_UNSAT_CORE, options).toArray(ProverOptions.class);
    try (ProverEnvironment prover = context.newProverEnvironment(options)) {
      // Try to report unsat core for failure message if the solver supports it.
      for (BooleanFormula formula : formulasUnderTest) {
        for (BooleanFormula part :
            context
                .getFormulaManager()
                .getBooleanFormulaManager()
                .toConjunctionArgs(formula, true)) {
          prover.push(part);
        }
      }
      if (!prover.isUnsat()) {
        throw new AssertionError("repeated satisfiability check returned different result");
      }
      final List<BooleanFormula> unsatCore = prover.getUnsatCore();
      if (unsatCore.isEmpty()
          || (unsatCore.size() == formulasUnderTest.size()
              && unsatCore.containsAll(formulasUnderTest))) {
        // empty or trivial unsat core
        failWithActual(Fact.fact("expected to be", "satisfiable"));
      } else {
        failWithoutActual(
            Fact.fact("expected to be", "satisfiable"),
            Fact.fact("but was", formulasUnderTest),
            Fact.fact("which has unsat core", Joiner.on('\n').join(unsatCore)));
      }
    } catch (UnsupportedOperationException ex) {

      // Otherwise just fail (unsat core not supported)
      failWithActual(Fact.fact("expected to be", "satisfiable"));
    }
  }

  /**
   * Check that the subjects are tautological, i.e., always holds. This is equivalent to calling
   * {@link #areEquivalentTo(BooleanFormula)} with the formula {@code true}, but it checks
   * satisfiability of the subjects and unsatisfiability of the negated subjects in two steps to
   * improve error messages.
   */
  public void areTautological(ProverOptions... options)
      throws SolverException, InterruptedException {
    BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    if (formulasUnderTest.stream().allMatch(bmgr::isFalse)) {
      failWithoutActual(
          Fact.fact("expected to be", "tautological"),
          Fact.fact("but was", "trivially unsatisfiable"));
      return;
    }

    // ¬(A ∧ B) == ¬A ∨ ¬B
    checkIsUnsat(
        ImmutableList.of(
            bmgr.or(Collections3.transformedImmutableListCopy(formulasUnderTest, bmgr::not))),
        Fact.fact("expected to be", "tautological"),
        options);
  }

  /**
   * Check that the conjunction of subjects are equivalent to the given formula, i.e. {@code
   * subjects <=> expected} always holds. Will show a counterexample on failure.
   */
  public void areEquivalentTo(final BooleanFormula expected)
      throws SolverException, InterruptedException {
    areEquivalentTo(ImmutableList.of(expected));
  }

  /**
   * Check that the conjunction of subjects is equivalent to the conjunction of given formulas, i.e.
   * {@code subjects <=> expected} always holds. Will show a counterexample on failure.
   */
  public void areEquivalentTo(final Collection<BooleanFormula> expected)
      throws SolverException, InterruptedException {

    if (HashMultiset.create(expected).equals(HashMultiset.create(formulasUnderTest))) {
      return;
    }

    BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    final BooleanFormula f = bmgr.xor(bmgr.and(formulasUnderTest), bmgr.and(expected));

    checkIsUnsat(ImmutableList.of(f), Fact.fact("expected to be equivalent to", expected));
  }

  public void areEquisatisfiableTo(BooleanFormula other)
      throws SolverException, InterruptedException {
    areEquisatisfiableTo(ImmutableList.of(other));
  }

  public void areEquisatisfiableTo(Collection<BooleanFormula> others)
      throws SolverException, InterruptedException {
    BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    checkIsUnsat(
        ImmutableList.of(bmgr.and(bmgr.and(formulasUnderTest), bmgr.not(bmgr.and(others)))),
        Fact.fact("expected to be equisatisfiable with", others));
  }

  /**
   * Check that the conjunction of subjects imply a given formula, i.e. {@code subjects => expected}
   * always holds. Will show a counterexample on failure.
   */
  public void imply(final BooleanFormula expected) throws SolverException, InterruptedException {
    imply(ImmutableList.of(expected));
  }

  /**
   * Check that the conjunction of subjects imply the conjunction of given formulas, i.e. {@code
   * subjects => expected} always holds. Will show a counterexample on failure.
   */
  public void imply(final Collection<BooleanFormula> expected)
      throws SolverException, InterruptedException {
    if (expected.containsAll(formulasUnderTest)) {
      return;
    }

    final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
    final BooleanFormula implication =
        bmgr.implication(bmgr.and(formulasUnderTest), bmgr.and(formulasUnderTest));

    checkIsUnsat(ImmutableList.of(bmgr.not(implication)), Fact.fact("expected to imply", expected));
  }
}
