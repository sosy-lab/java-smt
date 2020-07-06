// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

// reason: not maintained, some implementations for methods are missing
class LoggingSmtInterpolInterpolatingProver extends SmtInterpolInterpolatingProver {

  private final PrintWriter out;

  LoggingSmtInterpolInterpolatingProver(
      SmtInterpolFormulaManager pMgr, Set<ProverOptions> pOptions, PrintWriter pOut) {
    super(pMgr, pOptions);
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
    String result = super.addConstraint(f);
    out.println("(assert (! " + f + " :named " + result + "))");
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
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<String>> partitionedTermNames, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    Preconditions.checkArgument(partitionedTermNames.size() == startOfSubTree.length);
    out.print("(get-interpolants");
    Deque<Integer> subtrees = new ArrayDeque<>();
    for (int i = 0; i < startOfSubTree.length; i++) {
      final Collection<String> names = partitionedTermNames.get(i);
      final int currentStartOfSubtree = startOfSubTree[i];
      final String currentTerms;
      if (names.size() == 1) {
        currentTerms = names.iterator().next();
      } else {
        currentTerms = "(and " + Joiner.on(" ").join(names) + ")";
      }
      while (!subtrees.isEmpty() && subtrees.peek() > currentStartOfSubtree) {
        subtrees.pop();
        out.print(")");
      }
      out.print(" ");
      if (!subtrees.isEmpty() && subtrees.peek() < currentStartOfSubtree) {
        subtrees.push(currentStartOfSubtree);
        out.print("(");
      }
      if (subtrees.isEmpty()) {
        subtrees.push(currentStartOfSubtree);
      }

      out.print(currentTerms);
    }
    out.print(") ; subtrees=" + Arrays.toString(startOfSubTree));
    List<BooleanFormula> result = super.getTreeInterpolants(partitionedTermNames, startOfSubTree);
    out.println(" ; interpolants=" + result);
    return result;
  }

  @Override
  public void close() {
    out.close();
    super.close();
  }
}
