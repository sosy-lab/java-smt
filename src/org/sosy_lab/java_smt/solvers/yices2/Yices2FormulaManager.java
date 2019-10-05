/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_term;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class Yices2FormulaManager extends AbstractFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2FormulaManager(
      Yices2FormulaCreator pFormulaCreator,
      Yices2UFManager pFunctionManager,
      Yices2BooleanFormulaManager pBooleanManager,
      @Nullable Yices2IntegerFormulaManager pIntegerManager,
      @Nullable Yices2RationalFormulaManager pRationalManager,
      @Nullable Yices2BitvectorFormulaManager pBitvectorManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        null,
        null,
        null);
    // TODO Auto-generated constructor stub
  }

  static Integer getYicesTerm(Formula pT) {
    return ((Yices2Formula) pT).getTerm();
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Might expect Yices input language instead of smt-lib2 notation
    return getFormulaCreator().encapsulateBoolean(yices_parse_term(pS));
  }

  @Override
  public Appender dumpFormula(Integer pT) {
    // TODO Auto-generated method stub
    // VariableCollector
    return null;
  }

}
