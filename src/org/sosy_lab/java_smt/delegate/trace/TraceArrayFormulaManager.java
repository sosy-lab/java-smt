/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@SuppressWarnings("MethodTypeParameterName")
public class TraceArrayFormulaManager implements ArrayFormulaManager {
  private final ArrayFormulaManager delegate;
  private final TraceLogger logger;

  TraceArrayFormulaManager(ArrayFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    return logger.logDef(
        "mgr.getArrayFormulaManager()",
        String.format("select(%s, %s)", logger.toVariable(pArray), logger.toVariable(pIndex)),
        () -> delegate.select(pArray, pIndex));
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    return logger.logDef(
        "mgr.getArrayFormulaManager()",
        String.format(
            "store(%s, %s, %s)",
            logger.toVariable(pArray), logger.toVariable(pIndex), logger.toVariable(pValue)),
        () -> delegate.store(pArray, pIndex, pValue));
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    return logger.logDef(
        "mgr.getArrayFormulaManager()",
        String.format(
            "makeArray(\"%s\", %s, %s)",
            pName, logger.printFormulaType(pIndexType), logger.printFormulaType(pElementType)),
        () -> delegate.makeArray(pName, pIndexType, pElementType));
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE defaultElement) {
    return logger.logDef(
        "mgr.getArrayFormulaManager()",
        String.format(
            "makeArray(%s, %s, %s)",
            logger.printFormulaType(pIndexType),
            logger.printFormulaType(pElementType),
            logger.toVariable(defaultElement)),
        () -> delegate.makeArray(pIndexType, pElementType, defaultElement));
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    return logger.logDef(
        "mgr.getArrayFormulaManager()",
        String.format(
            "equivalence(%s, %s)", logger.toVariable(pArray1), logger.toVariable(pArray2)),
        () -> delegate.equivalence(pArray1, pArray2));
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    return delegate.getIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    return delegate.getElementType(pArray);
  }
}
