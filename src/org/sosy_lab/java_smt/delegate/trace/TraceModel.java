/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.Model;

class TraceModel extends TraceEvaluator implements Model {
  private final Model delegate;

  private final TraceFormulaManager mgr;
  private final TraceLogger logger;

  TraceModel(Model pDelegate, TraceFormulaManager pMgr, TraceLogger pLogger) {
    super(pDelegate, pMgr, pLogger);
    delegate = pDelegate;
    mgr = pMgr;
    logger = pLogger;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    ImmutableList<ValueAssignment> result =
        logger.logDefDiscard(logger.toVariable(this), "asList()", delegate::asList);
    return FluentIterable.from(result)
        .transform(
            (ValueAssignment assigment) -> {
              var key = mgr.rebuild(assigment.getKey());
              var val = mgr.rebuild(assigment.getValueAsFormula());
              var map = mgr.rebuild(assigment.getAssignmentAsFormula());
              return new ValueAssignment(
                  key,
                  val,
                  map,
                  assigment.getName(),
                  assigment.getValue(),
                  assigment.getArgumentsInterpretation());
            })
        .toList();
  }
}
