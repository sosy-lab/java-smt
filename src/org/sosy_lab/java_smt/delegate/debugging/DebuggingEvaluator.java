/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.debugging;

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
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.StringFormula;

public class DebuggingEvaluator implements Evaluator {
  private final Evaluator delegate;
  private final DebuggingAssertions debugging;

  DebuggingEvaluator(Evaluator pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    T result = delegate.eval(formula);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public @Nullable Object evaluate(Formula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(NumeralFormula.IntegerFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Rational evaluate(NumeralFormula.RationalFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(StringFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public void close() {
    debugging.assertThreadLocal();
    delegate.close();
  }
}
