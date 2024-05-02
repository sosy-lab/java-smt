// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public class DebuggingSLFormulaManager implements SLFormulaManager {
  private final SLFormulaManager delegate;
  private final DebuggingContext debugging;

  public DebuggingSLFormulaManager(SLFormulaManager pDelegate, DebuggingContext pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f1);
    debugging.assertFormulaInContext(f2);
    BooleanFormula result = delegate.makeStar(f1, f2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(ptr);
    debugging.assertFormulaInContext(to);
    BooleanFormula result = delegate.makePointsTo(ptr, to);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(f1);
    debugging.assertFormulaInContext(f2);
    BooleanFormula result = delegate.makeMagicWand(f1, f2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    debugging.assertThreadLocal();
    BooleanFormula result = delegate.makeEmptyHeap(pAdressType, pValueType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    debugging.assertThreadLocal();
    AF result = delegate.makeNilElement(pAdressType);
    debugging.addFormulaTerm(result);
    return result;
  }
}
