// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import edu.stanford.CVC4.Exception;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.ExprManagerMapCollection;
import edu.stanford.CVC4.Result;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;

class CVC4TheoremProver extends AbstractProverWithAllSat<Void>
    implements ProverEnvironment, BasicProverEnvironment<Void> {

  private final CVC4FormulaCreator creator;
  private final int randomSeed;
  SmtEngine smtEngine; // final except for SL theory

  /**
   * The local exprManager allows to set options per Prover (and not globally). See <a
   * href="https://github.com/CVC4/CVC4/issues/3055">Issue 3055</a> for details.
   *
   * <p>TODO If the overhead of importing/exporting the expressions is too expensive, we can disable
   * this behavior. This change would cost us the flexibility of setting options per Prover.
   */
  private ExprManager exprManager; // final except for SL theory

  /** We copy expression between different ExprManagers. The map serves as cache. */
  private ExprManagerMapCollection exportMapping; // final except for SL theory

  // CVC4 does not support separation logic in incremental mode.
  private final boolean incremental;

  protected CVC4TheoremProver(
      CVC4FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr) {
    super(pOptions, pBmgr, pShutdownNotifier);

    creator = pFormulaCreator;
    randomSeed = pRandomSeed;
    incremental = !enableSL;

    createNewEngine();
  }

  private void createNewEngine() {
    if (smtEngine != null) {
      smtEngine.delete(); // cleanup
    }
    if (exportMapping != null) {
      exportMapping.delete();
    }
    if (exprManager != null) {
      exprManager.delete(); // cleanup
    }
    exprManager = new ExprManager();
    smtEngine = new SmtEngine(exprManager);
    exportMapping = new ExprManagerMapCollection();
    smtEngine.setOption("incremental", new SExpr(incremental));
    smtEngine.setOption("produce-models", new SExpr(generateModels));
    smtEngine.setOption("produce-unsat-cores", new SExpr(generateUnsatCores));
    smtEngine.setOption("produce-assertions", new SExpr(true));
    smtEngine.setOption("dump-models", new SExpr(true));
    // smtEngine.setOption("produce-unsat-cores", new SExpr(true));
    smtEngine.setOption("output-language", new SExpr("smt2"));
    smtEngine.setOption("random-seed", new SExpr(randomSeed));
    // Set Strings option to enable all String features (such as lessOrEquals)
    smtEngine.setOption("strings-exp", new SExpr(true));
    // Enable more complete quantifier solving (for more information see
    // CVC4QuantifiedFormulaManager)
    smtEngine.setOption("full-saturate-quant", new SExpr(true));
  }

  /** import an expression from global context into this prover's context. */
  protected Expr importExpr(Expr expr) {
    return expr.exportTo(exprManager, exportMapping);
  }

  /** export an expression from this prover's context into global context. */
  protected Expr exportExpr(Expr expr) {
    return expr.exportTo(creator.getEnv(), exportMapping);
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    if (incremental) {
      smtEngine.push();
    }
  }

  @Override
  protected void popImpl() {
    if (incremental) {
      smtEngine.pop();
    }
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula pF) throws InterruptedException {
    Preconditions.checkState(!closed);
    if (incremental) {
      assertFormula(pF);
    }
    return null;
  }

  private void assertFormula(BooleanFormula pF) {
    try {
      smtEngine.assertFormula(importExpr(creator.extractInfo(pF)));
    } catch (Exception cvc4Exception) {
      throw new AssertionError(
          String.format("CVC4 crashed while adding the constraint '%s'", pF), cvc4Exception);
    }
  }

  @SuppressWarnings("resource")
  @Override
  public CVC4Model getModel() throws SolverException {
    checkGenerateModels();
    // special case for CVC4: Models are not permanent and need to be closed
    // before any change is applied to the prover stack. So, we register the Model as Evaluator.
    return registerEvaluator(
        new CVC4Model(
            this,
            creator,
            smtEngine,
            Collections2.transform(getAssertedFormulas(), creator::extractInfo)));
  }

  @Override
  public Evaluator getEvaluator() {
    checkGenerateModels();
    return getEvaluatorWithoutChecks();
  }

  @SuppressWarnings("resource")
  @Override
  protected Evaluator getEvaluatorWithoutChecks() {
    return registerEvaluator(new CVC4Evaluator(this, creator, smtEngine));
  }

  @Override
  protected boolean hasPersistentModel() {
    return false;
  }

  @Override
  @SuppressWarnings("try")
  protected boolean isUnsatImpl() throws InterruptedException, SolverException {
    closeAllEvaluators();

    if (!incremental) {
      // in non-incremental mode, we need to create a new solver instance for each sat check
      createNewEngine();
      getAssertedFormulas().forEach(this::assertFormula);
    }

    Result result;
    try (ShutdownHook hook = new ShutdownHook(shutdownNotifier, smtEngine::interrupt)) {
      shutdownNotifier.shutdownIfNecessary();
      result = smtEngine.checkSat();
    } catch (Exception e) {
      throw new SolverException("CVC4 failed during satisfiability check", e);
    } finally {
      shutdownNotifier.shutdownIfNecessary();
    }
    return convertSatResult(result);
  }

  private boolean convertSatResult(Result result) throws InterruptedException, SolverException {
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
    checkGenerateUnsatCores();
    List<BooleanFormula> converted = new ArrayList<>();
    for (Expr aCore : smtEngine.getUnsatCore()) {
      converted.add(creator.encapsulateBoolean(exportExpr(aCore)));
    }
    return converted;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(ASSUMPTION_SOLVING_NOT_SUPPORTED);
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(ASSUMPTION_SOLVING_NOT_SUPPORTED);
  }

  @Override
  public void close() {
    if (!closed) {
      exportMapping.delete();
      // smtEngine.delete();
      exprManager.delete();
    }
    super.close();
  }
}
