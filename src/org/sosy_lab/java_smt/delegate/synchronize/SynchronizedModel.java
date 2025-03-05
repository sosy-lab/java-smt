// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.StringFormula;

class SynchronizedModel implements Model {

  private final Model delegate;
  private final SolverContext sync;

  SynchronizedModel(Model pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T pFormula) {
    synchronized (sync) {
      return delegate.eval(pFormula);
    }
  }

  @Override
  public @Nullable Object evaluate(Formula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable String evaluate(StringFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula pF) {
    synchronized (sync) {
      return delegate.evaluate(pF);
    }
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    synchronized (sync) {
      return delegate.asList();
    }
  }

  @Override
  public void close() {
    synchronized (sync) {
      delegate.close();
    }
  }
}
