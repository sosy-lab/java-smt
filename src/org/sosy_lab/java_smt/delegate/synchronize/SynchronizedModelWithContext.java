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
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

class SynchronizedModelWithContext implements Model {

  private static final String UNSUPPORTED_OPERATION =
      "translating non-boolean formulae is not supported";

  private final Model delegate;
  private final SolverContext sync;
  private final FormulaManager manager;
  private final FormulaManager otherManager;

  SynchronizedModelWithContext(
      Model pDelegate, SolverContext pSync, FormulaManager pManager, FormulaManager pOtherManager) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
    manager = checkNotNull(pManager);
    otherManager = checkNotNull(pOtherManager);
  }

  @Override
  public <T extends Formula> @Nullable T eval(T pFormula) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Object evaluate(Formula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable BigInteger evaluate(IntegerFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Rational evaluate(RationalFormula pF) {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF)
      throws InterruptedException, SolverException {
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
  public ImmutableList<ValueAssignment> asList() {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
    // ImmutableList.Builder<ValueAssignment> builder = ImmutableList.builder();
    // ImmutableList<ValueAssignment> lst = delegate.asList();
    // synchronized (sync) {
    // for (ValueAssignment va : lst) {
    // if (va.getKey() instanceof BooleanFormula) {
    // builder.add(
    // new ValueAssignment(
    // manager.translateFrom((BooleanFormula) va.getKey(), otherManager),
    // manager.translateFrom((BooleanFormula) va.getValue(), otherManager),
    // manager.translateFrom(va.getAssignmentAsFormula(), otherManager),
    // va.getName(),
    // va.getValue(),
    // va.getArgumentsInterpretation()));
    // } else {
    // throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
    // }
    // }
    // }
    // return builder.build();
  }

  @Override
  public void close() {
    synchronized (sync) {
      delegate.close();
    }
  }
}
