/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.StringFormula;

class SynchronizedEvaluatorWithContext implements Evaluator {

  static final String UNSUPPORTED_OPERATION = "translating non-boolean formulae is not supported";

  private final Evaluator delegate;
  private final SolverContext sync;
  private final FormulaManager manager;
  private final FormulaManager otherManager;

  SynchronizedEvaluatorWithContext(
      Evaluator pDelegate,
      SolverContext pSync,
      FormulaManager pManager,
      FormulaManager pOtherManager) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
    manager = checkNotNull(pManager);
    otherManager = checkNotNull(pOtherManager);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> @Nullable T eval(T pFormula) {
    if (pFormula instanceof BooleanFormula booleanFormula) {
      BooleanFormula translated;
      synchronized (sync) {
        translated = otherManager.translateFrom(booleanFormula, manager);
      }
      BooleanFormula evaluated = delegate.eval(translated);
      synchronized (sync) {
        return (evaluated == null) ? null : (T) manager.translateFrom(evaluated, otherManager);
      }
    }
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Object evaluate(Formula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable BigInteger evaluate(NumeralFormula.IntegerFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Rational evaluate(NumeralFormula.RationalFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF) {
    BooleanFormula f;
    synchronized (sync) {
      f = otherManager.translateFrom(pF, manager);
    }
    return delegate.evaluate(f);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable String evaluate(StringFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public void close() {
    synchronized (sync) {
      delegate.close();
    }
  }
}
