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
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

public class DebuggingModel implements Model {
  private final Model delegate;
  private final DebuggingAssertions debugging;

  DebuggingModel(Model pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    T result = delegate.eval(formula);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public @Nullable Object evaluate(Formula formula) throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(StringFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula)
      throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(formula);
    return delegate.evaluate(formula);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() throws SolverException, InterruptedException {
    debugging.assertThreadLocal();
    ImmutableList<ValueAssignment> result = delegate.asList();
    for (ValueAssignment v : result) {
      // Both lines are needed as assignments like "a == false" may have been simplified to
      // "not(a)" by the solver. This then leads to errors as the term "false" is not defined in
      // the context.
      debugging.addFormulaTerm(v.getValueAsFormula());
      debugging.addFormulaTerm(v.getAssignmentAsFormula());
    }
    return result;
  }

  @Override
  public void close() {
    debugging.assertThreadLocal();
    delegate.close();
  }
}
