/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import ap.parser.IExpression;

import org.sosy_lab.solver.TermType;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

class PrincessFormulaCreator extends FormulaCreator<IExpression, TermType, PrincessEnvironment> {

  PrincessFormulaCreator(PrincessEnvironment pEnv, TermType pBoolType, TermType pIntegerType) {
    super(pEnv, pBoolType, pIntegerType, null);
  }

  @Override
  public FormulaType<?> getFormulaType(IExpression pFormula) {
    if (getEnv().hasArrayType(pFormula)) {
      return new ArrayFormulaType<>(FormulaType.IntegerType, FormulaType.IntegerType);
    } else if (PrincessUtil.isBoolean(pFormula)) {
      return FormulaType.BooleanType;
    } else if (PrincessUtil.hasIntegerType(pFormula)) {
      return FormulaType.IntegerType;
    }
    throw new IllegalArgumentException("Unknown formula type");
  }

  @Override
  public IExpression makeVariable(TermType type, String varName) {
    return getEnv().makeVariable(type, varName);
  }

  @Override
  public TermType getBitvectorType(int pBitwidth) {
    throw new UnsupportedOperationException("Bitvector theory is not supported by Princess");
  }

  @Override
  public TermType getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Princess");
  }

  @Override
  public TermType getArrayType(TermType pIndexType, TermType pElementType) {
    // no special cases here, princess does only support int arrays with int indexes
    return TermType.Array;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?>) {
      final FormulaType<?> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<?, ?>) pFormula);
      final FormulaType<?> arrayElementType =
          getArrayFormulaElementType((ArrayFormula<?, ?>) pFormula);
      return (FormulaType<T>) new ArrayFormulaType<>(arrayIndexType, arrayElementType);
    }

    return super.getFormulaType(pFormula);
  }
}
