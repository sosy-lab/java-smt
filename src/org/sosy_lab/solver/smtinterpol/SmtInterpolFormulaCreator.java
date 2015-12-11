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
package org.sosy_lab.solver.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

class SmtInterpolFormulaCreator extends FormulaCreator<Term, Sort, SmtInterpolEnvironment> {

  private final Sort booleanSort;
  private final Sort integerSort;
  private final Sort realSort;

  SmtInterpolFormulaCreator(final SmtInterpolEnvironment env) {
    super(env, env.getBooleanSort(), env.getIntegerSort(), env.getRealSort());
    booleanSort = env.getBooleanSort();
    integerSort = env.getIntegerSort();
    realSort = env.getRealSort();
  }

  @Override
  public FormulaType<?> getFormulaType(final Term pFormula) {
    return getFormulaTypeOfSort(pFormula.getSort());
  }

  private FormulaType<?> getFormulaTypeOfSort(final Sort pSort) {
    if (pSort == integerSort) {
      return FormulaType.IntegerType;
    } else if (pSort == realSort) {
      return FormulaType.RationalType;
    } else if (pSort == booleanSort) {
      return FormulaType.BooleanType;
    } else if (pSort.isArraySort()) {
      return new FormulaType.ArrayFormulaType<>(
          getFormulaTypeOfSort(pSort.getArguments()[0]),
          getFormulaTypeOfSort(pSort.getArguments()[1])
      );
    } else {
      throw new IllegalArgumentException("Unknown formula type for sort: " + pSort);
    }
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

  @Override
  public Term makeVariable(final Sort type, final String varName) {
    SmtInterpolEnvironment env = getEnv();
    env.declareFun(varName, new Sort[] {}, type);
    return env.term(varName);
  }

  @Override
  public Sort getBitvectorType(final int pBitwidth) {
    throw new UnsupportedOperationException(
        "Bitvector theory is not supported " + "by SmtInterpol");
  }

  @Override
  public Sort getFloatingPointType(final FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException(
        "FloatingPoint theory is not " + "supported by SmtInterpol");
  }

  @Override
  public Sort getArrayType(final Sort pIndexType, final Sort pElementType) {
    return getEnv().getTheory().getSort("Array", pIndexType, pElementType);
  }
}
