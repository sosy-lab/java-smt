// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;

class SynchronizedIntegerFormulaManager
    extends SynchronizedNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  private final IntegerFormulaManager delegate;

  SynchronizedIntegerFormulaManager(IntegerFormulaManager pDelegate, SolverContext pSync) {
    super(pDelegate, pSync);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula pNumber1, IntegerFormula pNumber2, BigInteger pN) {
    synchronized (sync) {
      return delegate.modularCongruence(pNumber1, pNumber2, pN);
    }
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula pNumber1, IntegerFormula pNumber2, long pN) {
    synchronized (sync) {
      return delegate.modularCongruence(pNumber1, pNumber2, pN);
    }
  }

  @Override
  public IntegerFormula modulo(IntegerFormula pNumber1, IntegerFormula pNumber2) {
    synchronized (sync) {
      return delegate.modulo(pNumber1, pNumber2);
    }
  }
}
