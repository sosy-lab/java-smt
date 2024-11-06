// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.math.BigInteger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.StringFormula;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractEvaluator<TFormulaInfo, TType, TEnv> implements Evaluator {

  private final AbstractProver<?> prover;
  protected final FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator;
  private boolean closed = false;

  protected AbstractEvaluator(
      AbstractProver<?> pProver, FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator) {
    this.prover = pProver;
    this.creator = creator;
  }

  @SuppressWarnings("unchecked")
  @Nullable
  @Override
  public final <T extends Formula> T eval(T f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    TFormulaInfo evaluation = evalImpl(creator.extractInfo(f));
    return evaluation == null ? null : (T) creator.encapsulateWithTypeOf(evaluation);
  }

  @Nullable
  @Override
  public final BigInteger evaluate(IntegerFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return (BigInteger) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public Rational evaluate(RationalFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    Object value = evaluateImpl(creator.extractInfo(f));
    if (value instanceof BigInteger) {
      // We simplified the value internally. Here, we need to convert it back to Rational.
      return Rational.ofBigInteger((BigInteger) value);
    } else {
      return (Rational) value;
    }
  }

  @Nullable
  @Override
  public final Boolean evaluate(BooleanFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return (Boolean) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public final String evaluate(StringFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return (String) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public final String evaluate(EnumerationFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return (String) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public final BigInteger evaluate(BitvectorFormula f) {
    Preconditions.checkState(!isClosed());
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return (BigInteger) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public final Object evaluate(Formula f) {
    Preconditions.checkState(!isClosed());
    Preconditions.checkArgument(
        !(f instanceof ArrayFormula),
        "cannot compute a simple constant evaluation for an array-formula");
    if (Generator.isLoggingEnabled()) {
      Generator.getLines().append("(get-value (" + f + "))\n");
    }
    return evaluateImpl(creator.extractInfo(f));
  }

  /**
   * Simplify the given formula and replace all symbols with their model values. If a symbol is not
   * set in the model and evaluation aborts, return <code>null</code>.
   */
  @Nullable
  protected abstract TFormulaInfo evalImpl(TFormulaInfo formula);

  /**
   * Simplify the given formula and replace all symbols with their model values. If a symbol is not
   * set in the model and evaluation aborts, return <code>null</code>. Afterwards convert the
   * formula into a Java object as far as possible, i.e., try to match a primitive or simple type.
   */
  @Nullable
  protected final Object evaluateImpl(TFormulaInfo f) {
    Preconditions.checkState(!isClosed());
    TFormulaInfo evaluatedF = evalImpl(f);
    return evaluatedF == null ? null : creator.convertValue(f, evaluatedF);
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public void close() {
    if (prover != null) { // can be NULL for testing
      prover.unregisterEvaluator(this);
    }
    closed = true;
  }
}
