// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public class DebuggingSLFormulaManager extends FormulaChecks implements SLFormulaManager {
  private final SLFormulaManager delegate;

  public DebuggingSLFormulaManager(SLFormulaManager pDelegate, Set<Formula> pformulasInContext) {
    super(pformulasInContext);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2) {
    assertThreadLocal();
    assertFormulaInContext(f1);
    assertFormulaInContext(f2);
    BooleanFormula result = delegate.makeStar(f1, f2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to) {
    assertThreadLocal();
    assertFormulaInContext(ptr);
    assertFormulaInContext(to);
    BooleanFormula result = delegate.makePointsTo(ptr, to);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2) {
    assertThreadLocal();
    assertFormulaInContext(f1);
    assertFormulaInContext(f2);
    BooleanFormula result = delegate.makeMagicWand(f1, f2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    assertThreadLocal();
    BooleanFormula result = delegate.makeEmptyHeap(pAdressType, pValueType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    assertThreadLocal();
    AF result = delegate.makeNilElement(pAdressType);
    addFormulaToContext(result);
    return result;
  }
}
