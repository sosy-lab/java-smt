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

package org.sosy_lab.java_smt.solvers.Solverless;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractSLFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverlessFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {
  /**
   * Builds a solver from the given theory implementations.
   *
   * @param pFormulaCreator
   * @param functionManager
   * @param booleanManager
   * @param pIntegerManager
   * @param pRationalManager
   * @param bitvectorManager
   * @param floatingPointManager
   * @param quantifiedManager
   * @param arrayManager
   * @param slManager
   * @param strManager
   * @param enumManager
   */
  protected SolverlessFormulaManager(
      FormulaCreator<Long, Long, Long, Long> pFormulaCreator,
      AbstractUFManager<Long, ?, Long, Long> functionManager,
      AbstractBooleanFormulaManager<Long, Long, Long, Long> booleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable AbstractBitvectorFormulaManager<Long, Long, Long, Long> bitvectorManager,
      @Nullable AbstractFloatingPointFormulaManager<Long, Long, Long, Long> floatingPointManager,
      @Nullable AbstractQuantifiedFormulaManager<Long, Long, Long, Long> quantifiedManager,
      @Nullable AbstractArrayFormulaManager<Long, Long, Long, Long> arrayManager,
      @Nullable AbstractSLFormulaManager<Long, Long, Long, Long> slManager,
      @Nullable AbstractStringFormulaManager<Long, Long, Long, Long> strManager,
      @Nullable AbstractEnumerationFormulaManager<Long, Long, Long, Long> enumManager) {
    super(pFormulaCreator, functionManager, booleanManager, pIntegerManager, pRationalManager,
        bitvectorManager, floatingPointManager, quantifiedManager, arrayManager, slManager,
        strManager, enumManager);
  }

  @Override
  public Appender dumpFormula(Long t) {
    return null;
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    return null;
  }
}
