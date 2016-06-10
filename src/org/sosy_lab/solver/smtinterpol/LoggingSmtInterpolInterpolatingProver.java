/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.smtinterpol;

import static com.google.common.base.Preconditions.checkNotNull;

import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;

import java.io.PrintWriter;

// reason: not maintained, some implementations for methods are missing
class LoggingSmtInterpolInterpolatingProver extends SmtInterpolInterpolatingProver {

  private final PrintWriter out;

  LoggingSmtInterpolInterpolatingProver(SmtInterpolFormulaManager pMgr, PrintWriter pOut) {
    super(pMgr);
    out = checkNotNull(pOut);
  }

  @Override
  public void pop() {
    out.println("(pop 1)");
    super.pop();
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    out.println("(check-sat)");
    return super.isUnsat();
  }

  @Override
  protected BooleanFormula getInterpolant(Term pTermA, Term pTermB)
      throws SolverException, InterruptedException {
    out.println("(get-interpolants " + pTermA + " " + pTermB + ")");
    return super.getInterpolant(pTermA, pTermB);
  }

  @Override
  public void close() {
    out.close();
    super.close();
  }
}
