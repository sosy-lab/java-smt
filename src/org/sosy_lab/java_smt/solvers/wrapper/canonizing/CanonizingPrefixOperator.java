/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.wrapper.canonizing;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingPrefixOperator implements CanonizingFormula {

  private static final long serialVersionUID = 1L;
  private transient FormulaManager mgr;
  private FormulaType<?> returnType;
  private FunctionDeclarationKind operator;
  private ImmutableList<CanonizingFormula> operands;
  private String name;

  private Integer hashCode = null;
  private transient Formula translated = null;

  private transient CanonizingFormula canonized = null;

  public final static CanonizingPrefixOperator getInstance(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType) {
    return getInstance(pMgr, pKind, pOperands, pReturnType, pKind.name());
  }

  public final static CanonizingPrefixOperator getInstance(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType,
      String pName) {
    if (pReturnType.isBooleanType()) {
      return new CanonizingBooleanPrefixOperator(pMgr, pKind, pOperands, pReturnType, pName);
    } else {
      return new CanonizingPrefixOperator(pMgr, pKind, pOperands, pReturnType, pName);
    }
  }

  private CanonizingPrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType) {
    this(pMgr, pKind, pOperands, pReturnType, pKind.name());
  }

  private CanonizingPrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pKind,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType,
      String pName) {
    mgr = pMgr;
    operator = pKind;
    operands = ImmutableList.copyOf(pOperands);
    returnType = pReturnType;
    name = pName;
  }

  @Override
  public CanonizingFormula getOperand1() {
    return operands.get(0);
  }

  @Override
  public CanonizingFormula getOperand2() {
    return operands.get(1);
  }

  @Override
  public CanonizingFormula getOperand3() {
    return operands.get(2);
  }

  public FunctionDeclarationKind getOperator() {
    return operator;
  }

  public CanonizingFormula getOperand(int pOperand) {
    return operands.get(pOperand);
  }

  @Override
  public CanonizingFormula copy() {
    List<CanonizingFormula> operandsCopy = new ArrayList<>();
    for (CanonizingFormula cf : operands) {
      operandsCopy.add(cf);
    }

    CanonizingFormula copy =
        new CanonizingPrefixOperator(mgr, operator, operandsCopy, returnType);

    return copy;
  }

  @Override
  public Formula toFormula(FormulaManager pMgr) {
    if (translated != null) {
      return translated;
    }

    if (operator == FunctionDeclarationKind.UF) {
      UFManager umgr = pMgr.getUFManager();
      List<Formula> args = new ArrayList<>();
      for (CanonizingFormula cf : operands) {
        args.add(cf.toFormula(pMgr));
      }

      translated = umgr.declareAndCallUF(name, returnType, args);
      return translated;
    }

    if (operator == FunctionDeclarationKind.ITE) {
      BooleanFormulaManager bmgr = pMgr.getBooleanFormulaManager();
      BooleanFormula formula0 = (BooleanFormula) operands.get(0).toFormula(pMgr);
      Formula formula1 = operands.get(1).toFormula(pMgr);
      Formula formula2 = operands.get(2).toFormula(pMgr);

      translated = bmgr.ifThenElse(formula0, formula1, formula2);
      return translated;
    }

    if (operator == FunctionDeclarationKind.FP_AS_BV) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula formula = (FloatingPointFormula) operands.get(0).toFormula(pMgr);

      translated = fmgr.toIeeeBitvector(formula);
      return translated;
    }

    if (operator == FunctionDeclarationKind.FP_FROM_BV) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      BitvectorFormula formula = (BitvectorFormula) operands.get(0).toFormula(pMgr);

      translated = fmgr.fromIeeeBitvector(formula, (FloatingPointType) returnType);
      return translated;
    }

    if (returnType.isBooleanType() && operands.get(0).getType().isFloatingPointType()) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      FloatingPointFormula[] fpOperands = new FloatingPointFormula[operands.size()];
      for (int i = 0; i < fpOperands.length; i++) {
        fpOperands[i] = (FloatingPointFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        case FP_IS_NAN:
          translated = fmgr.isNaN(fpOperands[0]);
          break;
        case FP_IS_INF:
          translated = fmgr.isInfinity(fpOperands[0]);
          break;
        case FP_IS_ZERO:
          translated = fmgr.isZero(fpOperands[0]);
          break;
        case FP_IS_SUBNORMAL:
          translated = fmgr.isSubnormal(fpOperands[0]);
          break;
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    }

    if (operator == FunctionDeclarationKind.NOT) {
      BooleanFormulaManager bmgr = pMgr.getBooleanFormulaManager();
      BooleanFormula formula0 = (BooleanFormula) operands.get(0).toFormula(pMgr);

      translated = bmgr.not(formula0);
      return translated;
    }

    // FIXME: function adaptation from PRINCESS
    if (operator == FunctionDeclarationKind.BV_SLT) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      BitvectorFormula formula0 = (BitvectorFormula) operands.get(1).toFormula(pMgr);
      BitvectorFormula formula1 = (BitvectorFormula) operands.get(2).toFormula(pMgr);

      translated = bmgr.lessThan(formula0, formula1, true);
      return translated;
    }

    if (operator == FunctionDeclarationKind.EQ_ZERO) {
      Formula formula = operands.get(0).toFormula(pMgr);
      FormulaType<?> type = operands.get(0).getType();

      translated = makeEqualZero(pMgr, formula, type);
      return translated;
    }

    if (operator == FunctionDeclarationKind.GTE_ZERO) {
      Formula formula = operands.get(0).toFormula(pMgr);
      FormulaType<?> type = operands.get(0).getType();

      translated = makeGreaterEqualZero(pMgr, formula, type);
      return translated;
    }

    if (isArrayOperator(operator)) {
      ArrayFormulaManager amgr = pMgr.getArrayFormulaManager();

      if (operator == FunctionDeclarationKind.SELECT) {
        @SuppressWarnings("unchecked")
        ArrayFormula<Formula, ?> array = (ArrayFormula<Formula, ?>) operands.get(0).toFormula(pMgr);
        Formula index = operands.get(1).toFormula(pMgr);

        translated = amgr.select(array, index);
      } else if (operator == FunctionDeclarationKind.STORE) {
        @SuppressWarnings("unchecked")
        ArrayFormula<Formula, Formula> array =
            (ArrayFormula<Formula, Formula>) operands.get(0).toFormula(pMgr);
        Formula index = operands.get(1).toFormula(pMgr);
        Formula value = operands.get(2).toFormula(pMgr);

        translated = amgr.store(array, index, value);
      }

      return translated;
    }

    if (returnType.isBitvectorType()) {
      BitvectorFormulaManager bmgr = pMgr.getBitvectorFormulaManager();
      Formula[] bvOperands = new Formula[operands.size()];
      for (int i = 0; i < bvOperands.length; i++) {
        bvOperands[i] = operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        case BV_EXTRACT:
          translated =
              bmgr.extract(
                  ((BitvectorFormula) bvOperands[0]),
                  ((Integer) ((CanonizingConstant) operands.get(1)).getValue()),
                  ((Integer) ((CanonizingConstant) operands.get(2)).getValue()),
                  true);
          break;
        case BV_SIGN_EXTENSION:
          translated =
              bmgr.extend(
                  ((BitvectorFormula) bvOperands[0]),
                  ((Integer) ((CanonizingConstant) operands.get(1)).getValue()),
                  true);
          break;
        case BV_ZERO_EXTENSION:
          translated =
              bmgr.extend(
              ((BitvectorFormula) bvOperands[0]),
              ((Integer) ((CanonizingConstant) operands.get(1)).getValue()),
              false);
          break;
        case BV_NEG:
          translated = bmgr.negate((BitvectorFormula) bvOperands[0]);
          break;
        case BV_ADD: // FIXME: PRINCESS
          translated = bmgr.add((BitvectorFormula) bvOperands[1], (BitvectorFormula) bvOperands[2]);
          break;
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isIntegerType()) {
      @SuppressWarnings("unused")
      IntegerFormulaManager bmgr = pMgr.getIntegerFormulaManager();
      IntegerFormula[] iOperands = new IntegerFormula[operands.size()];
      for (int i = 0; i < iOperands.length; i++) {
        iOperands[i] = (IntegerFormula) operands.get(i).toFormula(pMgr);
      }

      switch (operator) {
        default:
          throw new IllegalStateException(
              "Handling for PrefixOperator " + operator + " not yet implemented.");
      }
    } else if (returnType.isFloatingPointType()) {
      FloatingPointFormulaManager fmgr = pMgr.getFloatingPointFormulaManager();
      if (operator == FunctionDeclarationKind.BV_UCASTTO_FP) {
        Formula[] fOperands = new Formula[operands.size()];
        for (int i = 0; i < fOperands.length; i++) {
          fOperands[i] = operands.get(i).toFormula(pMgr);
        }

        translated = fmgr.castFrom(fOperands[1], false, (FormulaType.FloatingPointType) returnType);
      } else {
        FloatingPointFormula[] fpOperands = new FloatingPointFormula[operands.size()];
        for (int i = 0; i < fpOperands.length; i++) {
          fpOperands[i] = (FloatingPointFormula) operands.get(i).toFormula(pMgr);
        }

        switch (operator) {
          case FP_NEG:
            translated = fmgr.negate(fpOperands[0]);
            break;
          case FP_ROUND_AWAY:
            translated = fmgr.round(fpOperands[0], FloatingPointRoundingMode.NEAREST_TIES_AWAY);
            break;
          case FP_ROUND_EVEN:
            translated = fmgr.round(fpOperands[0], FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);
            break;
          case FP_ROUND_NEGATIVE:
            translated = fmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_NEGATIVE);
            break;
          case FP_ROUND_POSITIVE:
            translated = fmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_POSITIVE);
            break;
          case FP_ROUND_ZERO:
            translated = fmgr.round(fpOperands[0], FloatingPointRoundingMode.TOWARD_ZERO);
            break;
          case FP_MUL:
            translated = fmgr.multiply(fpOperands[1], fpOperands[2]);
            break;
          case FP_SUB:
            translated = fmgr.subtract(fpOperands[1], fpOperands[2]);
            break;
          case FP_ADD:
            translated = fmgr.add(fpOperands[1], fpOperands[2]);
            break;
          case FP_DIV:
            translated = fmgr.divide(fpOperands[1], fpOperands[2]);
            break;
          default:
            throw new IllegalStateException(
                "Handling for PrefixOperator " + operator + " not yet implemented.");
        }
      }
    }

    return translated;
  }

  private Formula
      makeGreaterEqualZero(FormulaManager pMgr, Formula pFormula, FormulaType<?> pType) {
    Formula result = null;

    if (pType.isArrayType()) {
      // TODO: this handling might be erroneous
      result = makeEqualZero(pMgr, pFormula, ((ArrayFormulaType<?, ?>) pType).getElementType());
    }
    // TODO: Is there an extra one in PRINCESS that holds the signedness?
    if (pType.isBitvectorType()) {
      result =
          pMgr.getBitvectorFormulaManager().greaterOrEquals(
              (BitvectorFormula) pFormula,
              pMgr.getBitvectorFormulaManager().makeBitvector(((BitvectorType) pType).getSize(), 0),
              false);
    }
    if (pType.isFloatingPointType()) {
      result =
          pMgr.getFloatingPointFormulaManager().greaterOrEquals(
              (FloatingPointFormula) pFormula,
              pMgr.getFloatingPointFormulaManager().makeNumber(0.0, ((FloatingPointType) pType)));
    }
    if (pType.isIntegerType()) {
      result =
          pMgr.getIntegerFormulaManager().greaterOrEquals(
              (IntegerFormula) pFormula,
              pMgr.getIntegerFormulaManager().makeNumber(0L));
    }
    if (pType.isRationalType()) {
      result =
          pMgr.getRationalFormulaManager().greaterOrEquals(
              (NumeralFormula) pFormula,
              pMgr.getRationalFormulaManager().makeNumber(0L));
    }

    return result;
  }

  private Formula makeEqualZero(FormulaManager pMgr, Formula formula, FormulaType<?> type) {
    Formula result = null;

    if (type.isArrayType()) {
      // TODO: this handling might be erroneous
      result = makeEqualZero(pMgr, formula, ((ArrayFormulaType<?, ?>) type).getElementType());
    }
    if (type.isBitvectorType()) {
      result =
          pMgr.getBitvectorFormulaManager().equal(
              (BitvectorFormula) formula,
              pMgr.getBitvectorFormulaManager()
                  .makeBitvector(((BitvectorType) type).getSize(), 0));
    }
    if (type.isFloatingPointType()) {
      result =
          pMgr.getFloatingPointFormulaManager().equalWithFPSemantics(
              (FloatingPointFormula) formula,
              pMgr.getFloatingPointFormulaManager().makeNumber(0.0, ((FloatingPointType) type)));
    }
    if (type.isIntegerType()) {
      result =
          pMgr.getIntegerFormulaManager()
              .equal((IntegerFormula) formula, pMgr.getIntegerFormulaManager().makeNumber(0L));
    }
    if (type.isRationalType()) {
      result =
          pMgr.getRationalFormulaManager()
              .equal((NumeralFormula) formula, pMgr.getRationalFormulaManager().makeNumber(0L));
    }
    return result;
  }

  private boolean isArrayOperator(FunctionDeclarationKind pOperator) {
    return pOperator == FunctionDeclarationKind.SELECT
        || pOperator == FunctionDeclarationKind.STORE;
  }

  @Override
  public CanonizingFormula canonize(CanonizingStrategy pStrategy, CanonizingFormulaStore pCaller) {
    if (canonized == null) {
      canonized = pStrategy.canonizePrefixOperator(mgr, operator, operands, returnType, pCaller);
    }
    return canonized;
  }

  @Override
  public FormulaType<?> getType() {
    return returnType;
  }

  @Override
  public FormulaManager getFormulaManager() {
    return mgr;
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append(operator).append(" ");
    for (CanonizingFormula cF : operands) {
      builder.append("_ ( ");
      cF.toString(builder);
      builder.append(" ) ");
    }

    return builder.toString();
  }

  @Override
  public void toString(StringBuilder pBuilder) {
    pBuilder.append("( ").append(name).append(" ");
    for (CanonizingFormula cF : operands) {
      pBuilder.append("_ ( ");
      cF.toString(pBuilder);
      pBuilder.append(" )");
    }
    pBuilder.append(" )");
  }

  @Override
  public int hashCode() {
    final int prime = 53;
    int result = 1;
    if (hashCode == null) {
      result = prime * result + ((operands == null) ? 0 : operands.hashCode());
      result = prime * result + ((operator == null) ? 0 : operator.hashCode());
      result = prime * result + ((returnType == null) ? 0 : returnType.hashCode());
      result = prime * result + ((name == null) ? 0 : name.hashCode());
      hashCode = result;
    }
    return hashCode;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (!(obj instanceof CanonizingPrefixOperator)) {
      return false;
    }
    CanonizingPrefixOperator other = (CanonizingPrefixOperator) obj;
    if (operands == null) {
      if (other.operands != null) {
        return false;
      }
    } else if (!operands.equals(other.operands)) {
      return false;
    }
    if (operator != other.operator) {
      return false;
    }
    if (returnType == null) {
      if (other.returnType != null) {
        return false;
      }
    } else if (!returnType.equals(other.returnType)) {
      return false;
    } else if (!name.equals(other.name)) {
      return false;
    }
    return true;
  }

  static final class CanonizingBooleanPrefixOperator extends CanonizingPrefixOperator
      implements BooleanFormula {

    private static final long serialVersionUID = 1L;

    private CanonizingBooleanPrefixOperator(
        FormulaManager pMgr,
        FunctionDeclarationKind pKind,
        List<CanonizingFormula> pOperands,
        FormulaType<?> pReturnType,
        String pName) {
      super(pMgr, pKind, pOperands, pReturnType, pName);
    }
  }
}
