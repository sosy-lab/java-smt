// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;


import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext;

class SynchronizedModelWithContext extends SynchronizedEvaluatorWithContext implements Model {

  SynchronizedModelWithContext(
      Model pDelegate, SolverContext pSync, FormulaManager pManager, FormulaManager pOtherManager) {
    super(pDelegate, pSync, pManager, pOtherManager);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
    // ImmutableList.Builder<ValueAssignment> builder = ImmutableList.builder();
    // ImmutableList<ValueAssignment> lst = delegate.asList();
    // synchronized (sync) {
    // for (ValueAssignment va : lst) {
    // if (va.getKey() instanceof BooleanFormula) {
    // builder.add(
    // new ValueAssignment(
    // manager.translateFrom((BooleanFormula) va.getKey(), otherManager),
    // manager.translateFrom((BooleanFormula) va.getValue(), otherManager),
    // manager.translateFrom(va.getAssignmentAsFormula(), otherManager),
    // va.getName(),
    // va.getValue(),
    // va.getArgumentsInterpretation()));
    // } else {
    // throw new UnsupportedOperationException(UNSUPPORTED_OPERATION);
    // }
    // }
    // }
    // return builder.build();
  }
}
