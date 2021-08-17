// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

class SynchronizedStringFormulaManager implements StringFormulaManager {

  private final StringFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedStringFormulaManager(StringFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public StringFormula makeString(String value) {
    synchronized (sync) {
      return delegate.makeString(value);
    }
  }

  @Override
  public StringFormula makeVariable(String pVar) {
    synchronized (sync) {
      return delegate.makeVariable(pVar);
    }
  }

  @Override
  public StringFormula equal(StringFormula str1, StringFormula str2) {
    synchronized (sync) {
      return delegate.equal(str1, str2);
    }
  }
}
