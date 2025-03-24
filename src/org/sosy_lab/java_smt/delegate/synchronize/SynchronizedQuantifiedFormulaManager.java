// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.IOException;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedQuantifiedFormulaManager implements QuantifiedFormulaManager {

  private final QuantifiedFormulaManager delegate;
  private final SolverContext sync;
  @SuppressWarnings("UnusedVariable")
  private ProverOptions[] option;

  SynchronizedQuantifiedFormulaManager(QuantifiedFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier pQ, List<? extends Formula> pVariables, BooleanFormula pBody) throws IOException {
    synchronized (sync) {
      return delegate.mkQuantifier(pQ, pVariables, pBody);
    }
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    synchronized (sync) {
      return delegate.eliminateQuantifiers(pF);
    }
  }

  @Override
  public void setOptions(ProverOptions... opt) {
    option = opt;
  }
}
