// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assert_;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.truth.Fact;
import com.google.common.truth.FailureMetadata;
import com.google.common.truth.StandardSubjectBuilder;
import com.google.common.truth.Subject;
import java.util.List;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * {@link Subject} subclass for testing assertions about ProverEnvironments with Truth (allows using
 * <code>assert_().about(...).that(stack).isUnsatisfiable()</code> etc.).
 *
 * <p>For a test use {@link SolverBasedTest0#assertThatEnvironment(BasicProverEnvironment)}, or
 * {@link StandardSubjectBuilder#about(com.google.common.truth.Subject.Factory)} and {@link
 * #proverEnvironments()}.
 */
public final class ProverEnvironmentSubject extends Subject {

  private final BasicProverEnvironment<?> stackUnderTest;

  private ProverEnvironmentSubject(FailureMetadata pMetadata, BasicProverEnvironment<?> pStack) {
    super(pMetadata, pStack);
    stackUnderTest = Preconditions.checkNotNull(pStack);
  }

  /**
   * Use this for checking assertions about ProverEnvironments with Truth: <code>
   * assert_().about(proverEnvironments()).that(stack).is...()</code>.
   */
  public static Subject.Factory<ProverEnvironmentSubject, BasicProverEnvironment<?>>
      proverEnvironments() {
    return ProverEnvironmentSubject::new;
  }

  /**
   * Use this for checking assertions about ProverEnvironments with Truth: <code>
   * assertThat(stack).is...()</code>.
   */
  public static ProverEnvironmentSubject assertThat(BasicProverEnvironment<?> prover) {
    return assert_().about(proverEnvironments()).that(prover);
  }

  /**
   * Check that the subject stack is unsatisfiable. Will show a model (satisfying assignment) on
   * failure.
   */
  public void isUnsatisfiable() throws SolverException, InterruptedException {
    if (stackUnderTest.isUnsat()) {
      return; // success
    }

    // get model for failure message
    try (Model model = stackUnderTest.getModel()) {
      failWithoutActual(
          Fact.fact("expected to be", "unsatisfiable"),
          Fact.fact("but was", stackUnderTest),
          Fact.fact("which is", "satisfiable"),
          Fact.fact("which has model", model));
    }
  }

  /** Check that the subject stack is satisfiable. Will show an unsat core on failure. */
  public void isSatisfiable() throws SolverException, InterruptedException {
    if (!stackUnderTest.isUnsat()) {
      return; // success
    }

    // get unsat core for failure message if possible
    if (stackUnderTest instanceof ProverEnvironment) {
      try {
        final List<BooleanFormula> unsatCore = stackUnderTest.getUnsatCore();
        if (!unsatCore.isEmpty()) {
          failWithoutActual(
              Fact.fact("expected to be", "satisfiable"),
              Fact.fact("but was", stackUnderTest),
              Fact.fact("which is", "unsatisfiable"),
              Fact.fact("with unsat core", Joiner.on('\n').join(unsatCore)));
          return;
        }
      } catch (IllegalArgumentException ignored) {
        // Skip if unsat core generation is disabled.
      }
    }
    failWithActual(Fact.fact("expected to be", "satisfiable"));
  }
}
