/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.UnsatCore;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;

abstract class CVC4AbstractProver<T, AF> implements BasicProverEnvironment<T> {

  protected final CVC4FormulaCreator creator;
  protected final SmtEngine smtEngine;

  protected final AtomicBoolean interrupted = new AtomicBoolean(false);
  protected boolean closed = false;

  /** track formulas on the stack, needed for model generation. */
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>();

  protected CVC4AbstractProver(
      CVC4FormulaCreator pFormulaCreator, ShutdownNotifier pShutdownNotifier, int randomSeed) {

    creator = pFormulaCreator;
    smtEngine = new SmtEngine(creator.getExprManager());

    setOptions(randomSeed);
    registerShutdownHandler(pShutdownNotifier);
  }

  private void setOptions(int randomSeed) {
    smtEngine.setOption("incremental", new SExpr(true));
    smtEngine.setOption("produce-models", new SExpr(true));
    smtEngine.setOption("produce-assertions", new SExpr(true));
    smtEngine.setOption("dump-models", new SExpr(true));
    // smtEngine.setOption("produce-unsat-cores", new SExpr(true));
    smtEngine.setOption("output-language", new SExpr("smt2"));
    smtEngine.setOption("random-seed", new SExpr(randomSeed));
  }

  // Due to a bug in CVC4, smtEngine.interrupt() has no effect when it is called too soon.
  // For example in the case of smtEngine.checkSat(), this is if interrupt() is called
  // before the line "Result result = d_propEngine->checkSat();" is called in the CVC4 C++
  // method SmtEngine::check(), which seems to take about 10 ms. When this is fixed in
  // CVC4, we can remove the Thread.sleep(10), the AtomicBoolean interrupted and the while
  // loop surrounding this block.
  private void registerShutdownHandler(ShutdownNotifier pShutdownNotifier) {
    pShutdownNotifier.register(
        (reason) -> {
          interrupted.set(true);
          while (interrupted.get()) {
            smtEngine.interrupt();
            try {
              Thread.sleep(10);
            } catch (InterruptedException e) {
            }
          }
        });
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    assertedFormulas.add(new ArrayList<>());
    smtEngine.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.pop();
    smtEngine.pop();
  }

  @Override
  public CVC4Model getModel() {
    Preconditions.checkState(!closed);
    return new CVC4Model(creator, smtEngine, getAssertedExpressions());
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    try (CVC4Model model = getModel()) {
      return model.modelToList();
    }
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Result result = smtEngine.checkSat();
    if (interrupted.get()) {
      interrupted.set(false); // Should we throw InterruptException?
    }
    if (result.isUnknown()) {
      if (result.whyUnknown().equals(Result.UnknownExplanation.INTERRUPTED)) {
        throw new InterruptedException();
      } else {
        throw new SolverException("CVC4 returned null or unknown on sat check (" + result + ")");
      }
    }
    if (result.isSat() == Result.Sat.SAT) {
      return false;
    } else if (result.isSat() == Result.Sat.UNSAT) {
      return true;
    } else {
      throw new SolverException("CVC4 returned unknown on sat check");
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    UnsatCore core = smtEngine.getUnsatCore();
    List<BooleanFormula> converted = new ArrayList<>();
    for (Expr aCore : core) {
      converted.add(creator.encapsulateBoolean(aCore));
    }
    return converted;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO inherit from ProverWithAllSat after merging from master-branch,
    // then we can remove this part.
    throw new UnsupportedOperationException();
  }

  protected abstract Collection<Expr> getAssertedExpressions();

  @Override
  public void close() {
    if (!closed) {
      assertedFormulas.clear();
      smtEngine.delete();
      closed = true;
    }
  }
}
