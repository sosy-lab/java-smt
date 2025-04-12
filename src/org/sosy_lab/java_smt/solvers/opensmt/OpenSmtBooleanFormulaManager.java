// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.util.Collection;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;

public class OpenSmtBooleanFormulaManager
    extends AbstractBooleanFormulaManager<PTRef, SRef, Logic, SymRef> {

  private final Logic logic;
  private final PTRef openSmtTrue;
  private final PTRef openSmtFalse;

  OpenSmtBooleanFormulaManager(OpenSmtFormulaCreator pCreator) {
    super(pCreator);
    logic = pCreator.getEnv();
    openSmtTrue = logic.getTerm_true();
    openSmtFalse = logic.getTerm_false();
  }

  @Override
  protected PTRef and(PTRef pParam1, PTRef pParam2) {
    return logic.mkAnd(pParam1, pParam2);
  }

  @Override
  protected PTRef andImpl(Collection<PTRef> pParams) {
    return logic.mkAnd(new VectorPTRef(pParams));
  }

  @Override
  protected PTRef equivalence(PTRef bits1, PTRef bits2) {
    return logic.mkEq(bits1, bits2);
  }

  @Override
  protected PTRef ifThenElse(PTRef pCond, PTRef pF1, PTRef pF2) {
    if (isTrue(pCond)) {
      return pF1;
    } else if (isFalse(pCond)) {
      return pF2;
    } else if (pF1.equals(pF2)) {
      return pF1;
    } else if (isTrue(pF1) && isFalse(pF2)) {
      return pCond;
    } else if (isFalse(pF1) && isTrue(pF2)) {
      return not(pCond);
    }
    return logic.mkIte(pCond, pF1, pF2);
  }

  @Override
  protected boolean isFalse(PTRef bits) {
    return logic.isFalse(bits);
  }

  @Override
  protected boolean isTrue(PTRef bits) {
    return logic.isTrue(bits);
  }

  @Override
  protected PTRef makeBooleanImpl(boolean value) {
    return value ? openSmtTrue : openSmtFalse;
  }

  @Override
  protected PTRef makeVariableImpl(String pVar) {
    try {
      return logic.mkBoolVar(pVar);
    } catch (UnsupportedOperationException e) {
      // can fail, if function is already declared with a different sort
      throw new IllegalArgumentException("Cannot declare boolean variable '" + pVar + "'", e);
    }
  }

  @Override
  protected PTRef not(PTRef pParam1) {
    return logic.mkNot(pParam1);
  }

  @Override
  protected PTRef or(PTRef pParam1, PTRef pParam2) {
    return logic.mkOr(pParam1, pParam2);
  }

  @Override
  protected PTRef orImpl(Collection<PTRef> pParams) {
    return logic.mkOr(new VectorPTRef(pParams));
  }

  @Override
  protected PTRef xor(PTRef pParam1, PTRef pParam2) {
    return logic.mkXor(pParam1, pParam2);
  }
}
