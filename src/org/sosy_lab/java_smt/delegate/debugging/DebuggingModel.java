// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.Model;

class DebuggingModel extends DebuggingEvaluator implements Model {
  private final Model delegate;
  private final DebuggingAssertions debugging;

  DebuggingModel(Model pDelegate, DebuggingAssertions pDebugging) {
    super(pDelegate, pDebugging);
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    debugging.assertThreadLocal();
    ImmutableList<ValueAssignment> result = delegate.asList();
    for (ValueAssignment v : result) {
      // Both lines are needed as assignments like "a == false" may have been simplified to
      // "not(a)" by the solver. This then leads to errors as the term "false" is not defined in
      // the context.
      debugging.addFormulaTerm(v.getValueAsFormula());
      debugging.addFormulaTerm(v.getAssignmentAsFormula());
    }
    return result;
  }
}
