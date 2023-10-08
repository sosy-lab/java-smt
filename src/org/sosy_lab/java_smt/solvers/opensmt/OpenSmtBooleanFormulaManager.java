// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import opensmt.Logic;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class OpenSmtBooleanFormulaManager
    extends AbstractBooleanFormulaManager<PTRef, SRef, Logic, SymRef> {

  private final Logic logic;

  OpenSmtBooleanFormulaManager(OpenSmtFormulaCreator pCreator) {
    super(pCreator);
    logic = pCreator.getEnv();
  }

  @Override
  protected PTRef and(PTRef pParam1, PTRef pParam2) {
    return logic.mkAnd(pParam1, pParam2);
  }

  @Override
  protected PTRef equivalence(PTRef bits1, PTRef bits2) {
    return logic.mkEq(bits1, bits2);
  }

  @Override
  protected PTRef ifThenElse(PTRef cond, PTRef f1, PTRef f2) {
    return logic.mkIte(cond, f1, f2);
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
    return value ? logic.getTerm_true() : logic.getTerm_false();
  }

  @Override
  protected PTRef makeVariableImpl(String pVar) {
    return logic.mkBoolVar(pVar);
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
  protected PTRef xor(PTRef pParam1, PTRef pParam2) {
    return logic.mkXor(pParam1, pParam2);
  }
}
