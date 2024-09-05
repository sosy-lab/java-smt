// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedOptimizationProverEnvironment extends SynchronizedBasicProverEnvironment<Formula>
    implements OptimizationProverEnvironment {

  private final OptimizationProverEnvironment delegate;

  SynchronizedOptimizationProverEnvironment(
      OptimizationProverEnvironment pDelegate, SolverContext pSync) {
    super(pDelegate, pSync);
    delegate = pDelegate;
  }

  @Override
  public int maximize(Formula pObjective) {
    synchronized (sync) {
      return delegate.maximize(pObjective);
    }
  }

  @Override
  public int minimize(Formula pObjective) {
    synchronized (sync) {
      return delegate.minimize(pObjective);
    }
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    synchronized (sync) {
      return delegate.check();
    }
  }

  @Override
  public Optional<Rational> upper(int pHandle, Rational pEpsilon) {
    synchronized (sync) {
      return delegate.upper(pHandle, pEpsilon);
    }
  }

  @Override
  public Optional<Rational> lower(int pHandle, Rational pEpsilon) {
    synchronized (sync) {
      return delegate.lower(pHandle, pEpsilon);
    }
  }
}
