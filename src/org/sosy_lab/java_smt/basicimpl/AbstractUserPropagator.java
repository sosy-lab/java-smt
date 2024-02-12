// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.UserPropagator;

public abstract class AbstractUserPropagator implements UserPropagator {

  private @Nullable PropagatorBackend backend;

  protected PropagatorBackend getBackend() {
    return Preconditions.checkNotNull(
        backend, "Trying to access an uninitialized user propagator.");
  }

  @Override
  public void onPush() {}

  @Override
  public void onPop(int numPoppedLevels) {}

  @Override
  public void onFinalCheck() {}

  @Override
  public void onKnownValue(BooleanFormula expr, boolean value) {}

  @Override
  public void onDecision(BooleanFormula expr, boolean value) {}

  @Override
  public void initializeWithBackend(PropagatorBackend pBackend) {
    Preconditions.checkState(
        this.backend == null,
        "Trying to register a user propagator that has been registered before.");
    this.backend = Preconditions.checkNotNull(pBackend);
  }

  @Override
  public void registerExpression(BooleanFormula theoryExpr) {
    Preconditions.checkState(
        backend != null,
        "Uninitialized backend. Make sure to register the user propagator with the prover"
            + "before calling this method.");
    backend.registerExpression(theoryExpr);
  }
}
