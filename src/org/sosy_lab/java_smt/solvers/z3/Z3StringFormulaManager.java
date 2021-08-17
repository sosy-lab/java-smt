// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 AlejandroSerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class Z3StringFormulaManager extends AbstractStringFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3StringFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
  }

  @Override
  protected Long makeStringImpl(String pValue) {
    return Native.mkString(z3context, pValue);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long equal(Long pParam1, Long pParam2) {
    return Native.mkEq(z3context, pParam1, pParam2);
  }
}
