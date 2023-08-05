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

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;

public class DReal4FormulaManager extends AbstractFormulaManager<DRealTerm<?, ?>, Type, Context,
    DRealTerm<?, ?>> {

  DReal4FormulaManager(DReal4FormulaCreator pFormulaCreator, DReal4UFManager pFunctionManager,
                       DReal4BooleanFormulaManager pBooleanManager,
                       DReal4IntegerFormulaManager pIntegerManager,
                       DReal4RationalFormulaManager pRationalManager,
                       DReal4QuantifiedFormulaManager pQuantifierManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        null,
        null,
        pQuantifierManager,
        null,
        null,
        null,
        null);
  }

  static DRealTerm<?, ?> getDReal4Formula(org.sosy_lab.java_smt.api.Formula pT) {
    if (pT instanceof DReal4Formula) {
      return ((DReal4Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    return null;
  }

  @Override
  public Appender dumpFormula(DRealTerm<?, ?> t) {
    return null;
  }

  @Override
  public <T extends Formula> T substitute(
      final T pF, final Map<? extends Formula, ? extends Formula> pFromToMapping) {
    DRealTerm<?, ?>[] changeFrom = new DRealTerm<?, ?>[pFromToMapping.size()];
    DRealTerm<?, ?>[] changeTo = new DRealTerm<?, ?>[pFromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : pFromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    DRealTerm<?, ?> f = extractInfo(pF);
    // Expected is a formula
    Preconditions.checkState(f.isFormula());
    org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula formula = f.getFormula();
    for (int i = 0; i < changeFrom.length; i++) {
      DRealTerm<?, ?> changeFromTerm = changeFrom[i];
      DRealTerm<?, ?> changeToTerm = changeTo[i];
      // Only Variables can be substituted
      Preconditions.checkState(changeFromTerm.isVar());
      if (changeToTerm.isVar()) {
        formula = formula.Substitute(changeFromTerm.getVariable(),
            new Expression(changeToTerm.getVariable()));
      } else if (changeToTerm.isExp()) {
        formula = formula.Substitute(changeFromTerm.getVariable(), changeToTerm.getExpression());
      } else {
        formula = formula.Substitute(changeFromTerm.getVariable(), changeToTerm.getFormula());
      }
    }
    FormulaType<T> type = getFormulaType(pF);
    return getFormulaCreator().encapsulate(type, new DRealTerm<>(formula, f.getType(),
        formula.get_kind()));
  }

}



