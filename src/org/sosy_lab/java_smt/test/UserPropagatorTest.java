// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import com.google.common.base.Verify;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

public class UserPropagatorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void init() {
    requireUserPropagators();
  }

  @Test
  public void testWithBlockedLiterals() throws SolverException, InterruptedException {
    // assert "p or q or r or s"
    BooleanFormula p = bmgr.makeVariable("p");
    BooleanFormula q = bmgr.makeVariable("q");
    BooleanFormula r = bmgr.makeVariable("r");
    BooleanFormula clause = bmgr.or(p, q, r);

    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(clause);
      // Create user propagator that prohibits variables to be set to true
      UserPropagator prop = new TestUserPropagator();
      Verify.verify(prover.registerUserPropagator(prop));
      prop.registerExpression(p);
      prop.registerExpression(q);
      prop.registerExpression(r);
      assertThatEnvironment(prover).isUnsatisfiable();
    }
  }

  /**
   * This user propagator will raise a conflict whenever a registered expression is set to true.
   */
  private static class TestUserPropagator extends AbstractUserPropagator {

    private final List<BooleanFormula> disabledExpressions = new ArrayList<>();

    @Override
    public void onKnownValue(BooleanFormula expr, boolean value) {
      if (value && disabledExpressions.contains(expr)) {
        getBackend().propagateConflict(new BooleanFormula[]{expr});
      }
    }

    @Override
    public void onDecision(BooleanFormula expr, boolean value) {
      for (BooleanFormula disExpr : disabledExpressions) {
        if (getBackend().propagateNextDecision(disExpr, Optional.of(true))) {
          break;
        }
      }
    }

    @Override
    public void initializeWithBackend(PropagatorBackend backend) {
      super.initializeWithBackend(backend);
      // Enable callbacks
      backend.notifyOnKnownValue();
      backend.notifyOnDecision();
    }

    @Override
    public void registerExpression(BooleanFormula theoryExpr) {
      disabledExpressions.add(theoryExpr);
      super.registerExpression(theoryExpr);
    }
  }
}
