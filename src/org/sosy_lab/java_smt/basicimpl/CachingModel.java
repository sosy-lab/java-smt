// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
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

public class CachingModel implements Model {

  private final Model delegate;

  private @Nullable ImmutableList<ValueAssignment> modelAssignments = null;

  public CachingModel(Model pDelegate) {
    delegate = Preconditions.checkNotNull(pDelegate);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() throws InterruptedException, SolverException {
    if (modelAssignments == null) {
      modelAssignments = delegate.asList();
    }
    return modelAssignments;
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <T extends Formula> @Nullable T eval(T formula)
      throws InterruptedException, SolverException {
    return delegate.eval(formula);
  }

  @Override
  public @Nullable Object evaluate(Formula formula) throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable BigInteger evaluate(BitvectorFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(StringFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable String evaluate(EnumerationFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public @Nullable FloatingPointNumber evaluate(FloatingPointFormula formula)
      throws InterruptedException, SolverException {
    return delegate.evaluate(formula);
  }

  @Override
  public String toString() {
    return delegate.toString();
  }
}
