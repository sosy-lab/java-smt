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
package org.sosy_lab.java_smt.solvers.opensmt2;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

final class OpensmtFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  // TODO: 5. IMPLEMENT
  protected OpensmtFormulaManager(
      OpensmtFormulaCreator pFormulaCreator,
      AbstractUFManager<Long, ?, Long, Long> pFunctionManager,
      OpensmtBooleanFormatManager pBooleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable AbstractBitvectorFormulaManager<Long, Long, Long, Long> pBitvectorManager,
      @Nullable AbstractFloatingPointFormulaManager<Long, Long, Long, Long> pFloatingPointManager,
      @Nullable AbstractQuantifiedFormulaManager<Long, Long, Long, Long> pQuantifiedManager,
      @Nullable AbstractArrayFormulaManager<Long, Long, Long, Long> pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        pFloatingPointManager,
        pQuantifiedManager,
        pArrayManager);
    // TODO Auto-generated constructor stub
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Appender dumpFormula(Long pT) {
    // TODO Auto-generated method stub
    return null;
  }
}
