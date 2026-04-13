// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

final class LeanSmtIntegerFormulaManager
    extends LeanSmtNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  LeanSmtIntegerFormulaManager(
      LeanSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected LeanSmtType getNumeralType() {
    return LeanSmtType.INT;
  }

  @Override
  protected FormulaType<?> getNumericFormulaType() {
    return FormulaType.IntegerType;
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, BigInteger pModulo) {
    return modularCongruence0(
        pNumber1, pNumber2, ((LeanSmtFormulaCreator) getFormulaCreator()).makeIntConstant(pModulo));
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    return modularCongruence0(
        pNumber1, pNumber2, ((LeanSmtFormulaCreator) getFormulaCreator()).makeIntConstant(pModulo));
  }

  private Long modularCongruence0(Long pNumber1, Long pNumber2, Long pModulo) {
    LeanSmtFormulaCreator creator = (LeanSmtFormulaCreator) getFormulaCreator();
    Long diff =
        creator.makeBinary(
            "-", FunctionDeclarationKind.SUB, FormulaType.IntegerType, pNumber1, pNumber2);
    Long remainder =
        creator.makeBinary(
            "mod", FunctionDeclarationKind.MODULO, FormulaType.IntegerType, diff, pModulo);
    Long zero = creator.makeIntConstant(0L);
    return creator.makeBinary(
        "=", FunctionDeclarationKind.EQ, FormulaType.BooleanType, remainder, zero);
  }
}
