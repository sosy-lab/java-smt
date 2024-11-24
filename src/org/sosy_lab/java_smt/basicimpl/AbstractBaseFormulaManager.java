// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

/**
 * A BaseFormulaManager because all Abstract*FormulaManager-Classes wrap a FormulaCreator-instance.
 *
 * @param <TFormulaInfo> the solver specific type.
 */
@SuppressWarnings("ClassTypeParameterName")
abstract class AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> {

  protected final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator;

  AbstractBaseFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator) {
    this.formulaCreator = pFormulaCreator;
  }

  protected final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> getFormulaCreator() {
    return formulaCreator;
  }

  protected final TFormulaInfo extractInfo(Formula pBits) {
    return getFormulaCreator().extractInfo(pBits);
  }

  final BooleanFormula wrapBool(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateBoolean(pTerm);
  }

  protected final TType toSolverType(FormulaType<?> formulaType) {
    TType t;
    if (formulaType.isBooleanType()) {
      t = getFormulaCreator().getBoolType();
    } else if (formulaType.isIntegerType()) {
      t = getFormulaCreator().getIntegerType();
    } else if (formulaType.isRationalType()) {
      t = getFormulaCreator().getRationalType();
    } else if (formulaType.isStringType()) {
      t = getFormulaCreator().getStringType();
    } else if (formulaType.isBitvectorType()) {
      FormulaType.BitvectorType bitPreciseType = (FormulaType.BitvectorType) formulaType;
      t = getFormulaCreator().getBitvectorType(bitPreciseType.getSize());
    } else if (formulaType.isFloatingPointType()) {
      FormulaType.FloatingPointType fpType = (FormulaType.FloatingPointType) formulaType;
      t = getFormulaCreator().getFloatingPointType(fpType);
    } else if (formulaType.isArrayType()) {
      FormulaType.ArrayFormulaType<?, ?> arrType = (FormulaType.ArrayFormulaType<?, ?>) formulaType;
      TType indexType = toSolverType(arrType.getIndexType());
      TType elementType = toSolverType(arrType.getElementType());
      t = getFormulaCreator().getArrayType(indexType, elementType);
    } else {
      throw new IllegalArgumentException("Not supported interface");
    }
    return t;
  }
}
