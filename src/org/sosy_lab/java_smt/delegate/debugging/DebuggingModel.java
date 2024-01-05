// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;

public class DebuggingModel extends FormulaChecks implements Model {
  private final Model delegate;

  public DebuggingModel(Model pDelegate, Set<Formula> pLocalFormula) {
    super(pLocalFormula);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    T result = delegate.eval(formula);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public @Nullable Object evaluate(Formula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(StringFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula) {
    assertThreadLocal();
    assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    assertThreadLocal();
    ImmutableList<ValueAssignment> result = delegate.asList();
    for (ValueAssignment v : result) {
      addFormulaToContext(v.getKey());
      addFormulaToContext(v.getValueAsFormula());
    }
    return result;
  }

  @Override
  public void close() {
    assertThreadLocal();
    delegate.close();
  }
}
