// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.sri.yices.Terms;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class Yices2BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Integer, Integer, Long, Integer> {

  Yices2BooleanFormulaManager(Yices2FormulaCreator pCreator) {
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
      return Terms.mkTrue();
    } else {
      return Terms.mkFalse();
    }
  }

  @Override
  protected Integer not(Integer pParam1) {
    return Terms.not(pParam1);
  }

  @Override
  protected Integer and(Integer pParam1, Integer pParam2) {
    return Terms.and(pParam1, pParam2);
  }

  @Override
  protected Integer or(Integer pParam1, Integer pParam2) {
    return Terms.or(pParam1, pParam2);
  }

  @Override
  protected Integer xor(Integer pParam1, Integer pParam2) {
    return Terms.xor(pParam1, pParam2);
  }

  @Override
  protected Integer equivalence(Integer pBits1, Integer pBits2) {
    return Terms.iff(pBits1, pBits2);
  }

  @Override
  protected Integer implication(Integer bits1, Integer bits2) {
    return Terms.implies(bits1, bits2);
  }

  @Override
  protected boolean isTrue(Integer pBits) {
    return pBits.equals(Terms.mkTrue());
  }

  @Override
  protected boolean isFalse(Integer pBits) {
    return pBits.equals(Terms.mkFalse());
  }

  @Override
  protected Integer ifThenElse(Integer pCond, Integer pF1, Integer pF2) {
    return Terms.ifThenElse(pCond, pF1, pF2);
  }
}
