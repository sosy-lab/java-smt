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
package org.sosy_lab.java_smt.solvers.stp;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public final class StpFormulaManager
    extends AbstractFormulaManager<Long, Long, Long, Long> {

  @SuppressWarnings("checkstyle:parameternumber")
  protected StpFormulaManager(
      FormulaCreator pFormulaCreator,
      // AbstractUFManager<Long, ?, Long, Long> pFunctionManager,
      StpBooleanFormulaManager pBooleanManager,
      // @Nullable IntegerFormulaManager pIntegerManager,
      // @Nullable RationalFormulaManager pRationalManager,
      @Nullable StpBitvectorFormulaManager pBitvectorManager,
      // @Nullable AbstractFloatingPointFormulaManager<Long, Long, Long, Long>
      // pFloatingPointManager,
      // @Nullable AbstractQuantifiedFormulaManager<Long, Long, Long, Long> pQuantifiedManager,
      @Nullable StpArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        null,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        null,
        null,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Implement parsing from SMTLIB-2 format to bool expr (I can see for BV and not Bool !)
    return null;
  }

  @Override
  public Appender dumpFormula(Long pT) {
    // TODO Implement - what does it do; ...
    return null;
  }
}
