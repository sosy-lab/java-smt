/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

/**
 * A BaseFormulaManager because all Abstract*FormulaManager-Classes wrap a FormulaCreator-instance.
 *
 * @param <TFormulaInfo> the solver specific type.
 */
abstract class AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> {

  protected final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator;

  AbstractBaseFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator) {
    this.formulaCreator = pFormulaCreator;
  }

  protected final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> getFormulaCreator() {
    return formulaCreator;
  }

  final TFormulaInfo extractInfo(Formula pBits) {
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

  protected static void checkVariableName(final String pVar) {
    Preconditions.checkArgument(!pVar.isEmpty(), "Identifier for variable should not be empty.");
    Preconditions.checkArgument(
        !Formula.BASIC_OPERATORS.contains(pVar), "Identifier should not be a simple operator.");
    Preconditions.checkArgument(
        !Formula.SMTLIB2_KEYWORDS.contains(pVar),
        "Identifier should not be a keyword of SMT-LIB2.");
    Preconditions.checkArgument(
        Iterables.all(Formula.DISALLOWED_CHARACTERS, c -> pVar.indexOf(c) == -1),
        "Identifier should contain an escape character of SMT-LIB2.");
  }
}
