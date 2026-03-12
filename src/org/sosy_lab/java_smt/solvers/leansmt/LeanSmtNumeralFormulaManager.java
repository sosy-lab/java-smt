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
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class LeanSmtNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Long, LeanSmtType, Long, ParamFormulaType, ResultFormulaType, LeanSmtFunctionDecl> {

  LeanSmtNumeralFormulaManager(
      LeanSmtFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  private LeanSmtFormulaCreator creator() {
    return (LeanSmtFormulaCreator) getFormulaCreator();
  }

  protected abstract LeanSmtType getNumeralType();

  protected abstract FormulaType<?> getNumericFormulaType();

  @SuppressWarnings("unchecked")
  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    return (FormulaType<ResultFormulaType>) getNumericFormulaType();
  }

  @Override
  protected boolean isNumeral(Long pVal) {
    LeanSmtFormulaCreator.Expr expr = creator().getExpression(pVal);
    return expr.kind == LeanSmtFormulaCreator.ExprKind.CONSTANT;
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected Long makeNumberImpl(long pI) {
    return makeNumberImpl(BigInteger.valueOf(pI));
  }

  @Override
  protected Long makeNumberImpl(BigInteger pI) {
    if (getNumeralType().isInt()) {
      return creator().makeIntConstant(pI);
    }
    return creator().makeRealConstant(Rational.ofBigInteger(pI));
  }

  @Override
  protected Long makeNumberImpl(String pI) {
    String normalized = pI.trim();
    if (normalized.contains("/")) {
      String[] parts = normalized.split("/", 2);
      if (getNumeralType().isInt()) {
        Long numerator = makeNumberImpl(new BigInteger(parts[0].trim()));
        Long denominator = makeNumberImpl(new BigInteger(parts[1].trim()));
        return divide(numerator, denominator);
      }
      return creator()
          .makeRealConstant(
              Rational.of(new BigInteger(parts[0].trim()), new BigInteger(parts[1].trim())));
    }
    if (normalized.contains(".") || normalized.contains("e") || normalized.contains("E")) {
      if (getNumeralType().isInt()) {
        return makeNumberImpl(decimalAsInteger(new BigDecimal(normalized)));
      }
      return creator().makeRealConstant(Rational.ofBigDecimal(new BigDecimal(normalized)));
    }
    return makeNumberImpl(new BigInteger(normalized));
  }

  @Override
  protected Long makeNumberImpl(Rational pNumber) {
    if (getNumeralType().isInt()) {
      if (pNumber.getDen().equals(BigInteger.ONE)) {
        return makeNumberImpl(pNumber.getNum());
      }
      return makeNumberImpl(pNumber.toString());
    }
    return creator().makeRealConstant(pNumber);
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    if (getNumeralType().isInt()) {
      return makeNumberImpl(decimalAsInteger(pNumber));
    }
    return makeNumberImpl(Rational.ofBigDecimal(pNumber));
  }

  @Override
  protected Long makeVariableImpl(String pI) {
    return creator().makeVariable(getNumeralType(), pI);
  }

  @Override
  public Long negate(Long pParam1) {
    return creator().makeUnary("-", FunctionDeclarationKind.UMINUS, getNumericFormulaType(), pParam1, LeanSmtNativeApi::mkNeg);
  }

  @Override
  public Long add(Long pParam1, Long pParam2) {
    return creator().makeBinary("+", FunctionDeclarationKind.ADD, getNumericFormulaType(), pParam1, pParam2, LeanSmtNativeApi::mkAdd);
  }

  @Override
  protected Long sumImpl(List<Long> pParams) {
    Long result = makeNumberImpl(0L);
    for (Long p : pParams) {
      result = add(result, p);
    }
    return result;
  }

  @Override
  public Long subtract(Long pParam1, Long pParam2) {
    return creator().makeBinary("-", FunctionDeclarationKind.SUB, getNumericFormulaType(), pParam1, pParam2, LeanSmtNativeApi::mkSub);
  }

  @Override
  public Long multiply(Long pParam1, Long pParam2) {
    return creator().makeBinary("*", FunctionDeclarationKind.MUL, getNumericFormulaType(), pParam1, pParam2, LeanSmtNativeApi::mkMul);
  }

  @Override
  public Long divide(Long pParam1, Long pParam2) {
    if (getNumeralType().isReal()) {
      return creator()
          .makeBinary(
              "/",
              FunctionDeclarationKind.DIV,
              getNumericFormulaType(),
              pParam1,
              pParam2,
              (a, b) -> LeanSmtNativeApi.mkApp2("/", a, b));
    }
    return creator()
        .makeBinary(
            "div",
            FunctionDeclarationKind.DIV,
            getNumericFormulaType(),
            pParam1,
            pParam2,
            LeanSmtNativeApi::mkDiv);
  }

  @Override
  public Long modulo(Long pParam1, Long pParam2) {
    return creator().makeBinary("mod", FunctionDeclarationKind.MODULO, getNumericFormulaType(), pParam1, pParam2, LeanSmtNativeApi::mkMod);
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, BigInteger pModulo) {
    throw new UnsupportedOperationException("LeanSMT backend does not support modular congruence yet");
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    throw new UnsupportedOperationException("LeanSMT backend does not support modular congruence yet");
  }

  @Override
  public Long equal(Long pParam1, Long pParam2) {
    return creator().makeBinary("=", FunctionDeclarationKind.EQ, FormulaType.BooleanType, pParam1, pParam2, LeanSmtNativeApi::mkEq);
  }

  @Override
  protected Long distinctImpl(List<Long> pNumbers) {
    if (pNumbers.size() < 2) {
      return creator().getTrueHandle();
    }
    Long result = null;
    for (int i = 0; i < pNumbers.size(); i++) {
      for (int j = i + 1; j < pNumbers.size(); j++) {
        Long next =
            creator()
                .makeBinary(
                    "distinct",
                    FunctionDeclarationKind.DISTINCT,
                    FormulaType.BooleanType,
                    pNumbers.get(i),
                    pNumbers.get(j),
                    LeanSmtNativeApi::mkDistinct);
        if (result == null) {
          result = next;
        } else {
          result =
              creator()
                  .makeBinary(
                      "and",
                      FunctionDeclarationKind.AND,
                      FormulaType.BooleanType,
                      result,
                      next,
                      LeanSmtNativeApi::mkAnd);
        }
      }
    }
    return result == null ? creator().getTrueHandle() : result;
  }

  @Override
  public Long greaterThan(Long pParam1, Long pParam2) {
    return creator().makeBinary(">", FunctionDeclarationKind.GT, FormulaType.BooleanType, pParam1, pParam2, LeanSmtNativeApi::mkGt);
  }

  @Override
  public Long greaterOrEquals(Long pParam1, Long pParam2) {
    return creator().makeBinary(">=", FunctionDeclarationKind.GTE, FormulaType.BooleanType, pParam1, pParam2, LeanSmtNativeApi::mkGe);
  }

  @Override
  public Long lessThan(Long pParam1, Long pParam2) {
    return creator().makeBinary("<", FunctionDeclarationKind.LT, FormulaType.BooleanType, pParam1, pParam2, LeanSmtNativeApi::mkLt);
  }

  @Override
  public Long lessOrEquals(Long pParam1, Long pParam2) {
    return creator().makeBinary("<=", FunctionDeclarationKind.LTE, FormulaType.BooleanType, pParam1, pParam2, LeanSmtNativeApi::mkLe);
  }

  @Override
  protected Long floor(Long pNumber) {
    if (getNumeralType().isInt()) {
      return pNumber;
    }
    return creator().makeFloorTerm(pNumber);
  }
}
