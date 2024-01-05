// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class DebuggingIntegerFormulaManager
    extends DebuggingNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {
  private final IntegerFormulaManager delegate;

  public DebuggingIntegerFormulaManager(
      IntegerFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pDelegate, pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.modularCongruence(number1, number2, n);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.modularCongruence(number1, number2, n);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denumerator) {
    assertThreadLocal();
    assertFormulaInContext(numerator);
    assertFormulaInContext(denumerator);
    IntegerFormula result = delegate.modulo(numerator, denumerator);
    addFormulaToContext(result);
    return result;
  }
}
