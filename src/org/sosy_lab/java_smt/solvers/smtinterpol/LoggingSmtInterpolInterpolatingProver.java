/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Joiner;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.io.PrintWriter;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

// reason: not maintained, some implementations for methods are missing
class LoggingSmtInterpolInterpolatingProver extends SmtInterpolInterpolatingProver {

  private final PrintWriter out;

  LoggingSmtInterpolInterpolatingProver(SmtInterpolFormulaManager pMgr, PrintWriter pOut) {
    super(pMgr);
    out = checkNotNull(pOut);
  }

  @Override
  public void push() {
    out.println("(push 1)");
    super.push();
  }

  @Override
  public void pop() {
    out.println("(pop 1)");
    super.pop();
  }

  @Override
  public String addConstraint(BooleanFormula f) {
    out.print("(assert (" + f + "))");
    String result = super.addConstraint(f);
    out.print(" ; annotated term: " + result);
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    out.println("(get-unsat-core)");
    return super.getUnsatCore();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> predicates)
      throws InterruptedException, SolverException {
    out.println("(all-sat (" + Joiner.on(", ").join(predicates) + "))");
    return super.allSat(callback, predicates);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    out.print("(check-sat)");
    boolean isUnsat = super.isUnsat();
    out.println(" ; " + (isUnsat ? "UNSAT" : "SAT"));
    return isUnsat;
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
