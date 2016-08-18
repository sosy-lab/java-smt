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

import com.google.common.truth.FailureStrategy;
import com.google.common.truth.Subject;
import com.google.common.truth.SubjectFactory;
import com.google.common.truth.TestVerb;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

import java.util.List;

/**
 * {@link Subject} subclass for testing assertions about ProverEnvironments with Truth
 * (allows to use <code>assert_().about(...).that(stack).isUnsatisfiable()</code> etc.).
 *
 * <p>Use {@link SolverBasedTest0#assertThatEnvironment(BasicProverEnvironment)},
 * or {@link TestVerb#about(com.google.common.truth.SubjectFactory)} and
 * {@link #proverEnvironment()}.
 */
@SuppressFBWarnings("EQ_DOESNT_OVERRIDE_EQUALS")
public class ProverEnvironmentSubject
    extends Subject<ProverEnvironmentSubject, BasicProverEnvironment<?>> {

  private ProverEnvironmentSubject(
      FailureStrategy pFailureStrategy, BasicProverEnvironment<?> pStack) {
    super(pFailureStrategy, pStack);
  }

  /**
   * Use this for checking assertions about ProverEnvironments with Truth:
   * <code>assert_().about(proverEnvironment()).that(stack).is...()</code>.
   */
  public static SubjectFactory<ProverEnvironmentSubject, BasicProverEnvironment<?>>
      proverEnvironment() {
    return new SubjectFactory<ProverEnvironmentSubject, BasicProverEnvironment<?>>() {
      @Override
      public ProverEnvironmentSubject getSubject(
          FailureStrategy pFs, BasicProverEnvironment<?> pFormula) {
        return new ProverEnvironmentSubject(pFs, pFormula);
      }
    };
  }

  /**
   * Check that the subject stack is unsatisfiable.
   * Will show a model (satisfying assignment) on failure.
   */
  public void isUnsatisfiable() throws SolverException, InterruptedException {
    if (getSubject().isUnsat()) {
      return; // success
    }

    // get model for failure message
    try (final Model model = getSubject().getModel()) {
      failWithBadResults("is", "unsatisfiable", "has counterexample", model);
    }
  }

  /**
   * Check that the subject stack is satisfiable.
   * Will show an unsat core on failure.
   */
  public void isSatisfiable() throws SolverException, InterruptedException {
    if (!getSubject().isUnsat()) {
      return; // success
    }

    // get unsat core for failure message if possible
    if (getSubject() instanceof ProverEnvironment) {
      try {
        final List<BooleanFormula> unsatCore = ((ProverEnvironment) getSubject()).getUnsatCore();
        if (!unsatCore.isEmpty()) {
          failWithBadResults("is", "satisfiable", "has unsat core", unsatCore);
          return;
        }
      } catch (IllegalArgumentException ignored) {
        // Skip if unsat core generation is disabled.
      }
    }
    fail("is", "satisfiable");
  }
}
