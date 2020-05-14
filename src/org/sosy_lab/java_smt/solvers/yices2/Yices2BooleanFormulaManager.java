/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_iff;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ite;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_xor2;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class Yices2BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2BooleanFormulaManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Integer makeVariableImpl(String pVar) {
    int boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Integer makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return yices_true();
    } else {
      return yices_false();
    }
  }

  @Override
  protected Integer not(Integer pParam1) {
    return yices_not(pParam1);
  }

  @Override
  protected Integer and(Integer pParam1, Integer pParam2) {
    return yices_and2(pParam1, pParam2);
  }
  // Causes BooleanFormulaManagerTest/testConjunctionCollector to fail.
  // @Override
  // protected Integer andImpl(Collection<Integer> pParams) {
  // return yices_and(pParams.size(), Ints.toArray(pParams));
  // }

  @Override
  protected Integer or(Integer pParam1, Integer pParam2) {
    return yices_or2(pParam1, pParam2);
  }

  // Causes BooleanFormulaManagerTest/testDisjunctionCollector to fail.
  // @Override
  // protected Integer orImpl(Collection<Integer> pParams) {
  // return yices_or(pParams.size(), Ints.toArray(pParams));
  // }

  @Override
  protected Integer xor(Integer pParam1, Integer pParam2) {
    return yices_xor2(pParam1, pParam2);
  }

  @Override
  protected Integer equivalence(Integer pBits1, Integer pBits2) {
    return yices_iff(pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Integer pBits) {
    return pBits.equals(yices_true());
  }

  @Override
  protected boolean isFalse(Integer pBits) {
    return pBits.equals(yices_false());
  }

  @Override
  protected Integer ifThenElse(Integer pCond, Integer pF1, Integer pF2) {
    return yices_ite(pCond, pF1, pF2);
  }
}
