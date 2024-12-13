// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.ExpectFailure.assertThat;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.proverEnvironments;

import com.google.common.base.Throwables;
import com.google.common.truth.ExpectFailure;
import com.google.common.truth.ExpectFailure.SimpleSubjectBuilderCallback;
import com.google.common.truth.SimpleSubjectBuilder;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedInterpolatingSolverBasedTest0;

public class ProverEnvironmentSubjectTestInterpolating
    extends ParameterizedInterpolatingSolverBasedTest0 {

  private BooleanFormula simpleFormula;
  private BooleanFormula contradiction;

  @Before
  public void setupFormulas() {
    if (imgr != null) {
      simpleFormula = imgr.equal(imgr.makeVariable("a"), imgr.makeNumber(1));
      contradiction =
          bmgr.and(simpleFormula, imgr.equal(imgr.makeVariable("a"), imgr.makeNumber(2)));
    } else {
      simpleFormula = bvmgr.equal(bvmgr.makeVariable(2, "a"), bvmgr.makeBitvector(2, 1));
      contradiction =
          bmgr.and(
              simpleFormula, bvmgr.equal(bvmgr.makeVariable(2, "a"), bvmgr.makeBitvector(2, 2)));
    }
  }

  @Test
  public void testIsSatisfiableYes() throws SolverException, InterruptedException {
    try (ProverEnvironment env = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      env.push(simpleFormula);
      assertThatEnvironment(env).isSatisfiable();
    }
  }

  @Test
  public void testIsSatisfiableNo() throws InterruptedException {
    requireUnsatCore();
    try (ProverEnvironment env =
        context.newProverEnvironment(
            ProverOptions.GENERATE_MODELS, ProverOptions.GENERATE_UNSAT_CORE)) {
      env.push(contradiction);
      AssertionError failure = expectFailure(whenTesting -> whenTesting.that(env).isSatisfiable());
      assertThat(failure).factValue("with unsat core").isNotEmpty();
    }
  }

  @Test
  public void testIsUnsatisfiableYes() throws SolverException, InterruptedException {
    try (ProverEnvironment env = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      env.push(contradiction);
      assertThatEnvironment(env).isUnsatisfiable();
    }
  }

  @Test
  public void testIsUnsatisfiableNo() throws InterruptedException {
    requireModel();
    try (ProverEnvironment env = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      env.push(simpleFormula);
      AssertionError failure =
          expectFailure(whenTesting -> whenTesting.that(env).isUnsatisfiable());
      assertThat(failure).factValue("which has model").isNotEmpty();
    }
  }

  private AssertionError expectFailure(ExpectFailureCallback expectFailureCallback) {
    return ExpectFailure.expectFailureAbout(proverEnvironments(), expectFailureCallback);
  }

  /** Variant of {@link SimpleSubjectBuilderCallback} that allows checked exception. */
  private interface ExpectFailureCallback
      extends SimpleSubjectBuilderCallback<ProverEnvironmentSubject, BasicProverEnvironment<?>> {

    void invokeAssertionUnchecked(
        SimpleSubjectBuilder<ProverEnvironmentSubject, BasicProverEnvironment<?>> pWhenTesting)
        throws Exception;

    @Override
    default void invokeAssertion(
        SimpleSubjectBuilder<ProverEnvironmentSubject, BasicProverEnvironment<?>> pWhenTesting) {
      try {
        invokeAssertionUnchecked(pWhenTesting);
      } catch (Exception e) {
        Throwables.throwIfUnchecked(e);
        throw new RuntimeException(e);
      }
    }
  }
}
