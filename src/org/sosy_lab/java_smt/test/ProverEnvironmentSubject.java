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

import static com.google.common.truth.Truth.assert_;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.truth.Fact;
import com.google.common.truth.FailureMetadata;
import com.google.common.truth.StandardSubjectBuilder;
import com.google.common.truth.Subject;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.List;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * {@link Subject} subclass for testing assertions about ProverEnvironments with Truth (allows to
 * use <code>assert_().about(...).that(stack).isUnsatisfiable()</code> etc.).
 *
 * <p>For a test use {@link SolverBasedTest0#assertThatEnvironment(BasicProverEnvironment)}, or
 * {@link StandardSubjectBuilder#about(com.google.common.truth.Subject.Factory)} and {@link
 * #proverEnvironments()}.
 */
@SuppressFBWarnings("EQ_DOESNT_OVERRIDE_EQUALS")
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
    return (metadata, formula) -> new ProverEnvironmentSubject(metadata, formula);
  }

  /**
   * Use this for checking assertions about ProverEnvironments with Truth: <code>
   * assertThat(stack).is...()</code>.
   */
  public static final ProverEnvironmentSubject assertThat(BasicProverEnvironment<?> prover) {
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
