// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.trace;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings("MethodTypeParameterName")
public class TraceSLFormulaManager implements SLFormulaManager {

  private final SLFormulaManager delegate;
  private final TraceLogger logger;

  TraceSLFormulaManager(SLFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = checkNotNull(pDelegate);
    logger = checkNotNull(pLogger);
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2) {
    return logger.logDef(
        "mgr.getSLFormulaManager()",
        String.format("makeStar(%s, %s)", logger.toVariable(f1), logger.toVariable(f2)),
        () -> delegate.makeStar(f1, f2));
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to) {
    return logger.logDef(
        "mgr.getSLFormulaManager()",
        String.format("makePointsTo(%s, %s)", logger.toVariable(ptr), logger.toVariable(to)),
        () -> delegate.makePointsTo(ptr, to));
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2) {
    return logger.logDef(
        "mgr.getSLFormulaManager()",
        String.format("makeMagicWand(%s, %s)", logger.toVariable(f1), logger.toVariable(f2)),
        () -> delegate.makeMagicWand(f1, f2));
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAddressType, VT pValueType) {
    return logger.logDef(
        "mgr.getSLFormulaManager()",
        String.format(
            "makeEmptyHeap(%s, %s)",
            logger.printFormulaType(pAddressType), logger.printFormulaType(pValueType)),
        () -> delegate.makeEmptyHeap(pAddressType, pValueType));
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAddressType) {
    return logger.logDef(
        "mgr.getSLFormulaManager()",
        String.format("makeNilElement(%s)", logger.printFormulaType(pAddressType)),
        () -> delegate.makeNilElement(pAddressType));
  }
}
