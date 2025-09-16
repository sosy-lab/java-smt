// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.CVC4JNI;
import edu.stanford.CVC4.Configuration;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import java.util.Set;
import java.util.function.Consumer;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC4SolverContext extends AbstractSolverContext {

  // creator is final, except after closing, then null.
  private CVC4FormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;

  private CVC4SolverContext(
      CVC4FormulaCreator creator,
      CVC4FormulaManager manager,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed) {
    super(manager);
    this.creator = creator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
  }

  public static SolverContext create(
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Consumer<String> pLoader) {

    pLoader.accept("cvc4jni");

    // ExprManager is the central class for creating expressions/terms/formulae.
    ExprManager exprManager = new ExprManager();
    CVC4FormulaCreator creator = new CVC4FormulaCreator(exprManager);

    // set common options.
    // temporary SmtEngine instance, until ExprManager.getOptions() works without SegFault.
    SmtEngine smtEngine = new SmtEngine(exprManager);
    smtEngine.setOption("output-language", new SExpr("smt2"));
    smtEngine.setOption("random-seed", new SExpr(randomSeed));
    // Set Strings option to enable all String features (such as lessOrEquals)
    smtEngine.setOption("strings-exp", new SExpr(true));
    // smtEngine.delete();

    // Create managers
    CVC4UFManager functionTheory = new CVC4UFManager(creator);
    CVC4BooleanFormulaManager booleanTheory = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager integerTheory =
        new CVC4IntegerFormulaManager(creator, pNonLinearArithmetic);
    CVC4RationalFormulaManager rationalTheory =
        new CVC4RationalFormulaManager(creator, pNonLinearArithmetic);
    CVC4BitvectorFormulaManager bitvectorTheory =
        new CVC4BitvectorFormulaManager(creator, booleanTheory);

    CVC4FloatingPointFormulaManager fpTheory;
    if (Configuration.isBuiltWithSymFPU()) {
      fpTheory = new CVC4FloatingPointFormulaManager(creator, pFloatingPointRoundingMode);
    } else {
      fpTheory = null;
      pLogger.log(Level.INFO, "CVC4 was built without support for FloatingPoint theory");
      // throw new AssertionError("CVC4 was built without support for FloatingPoint theory");
    }

    CVC4QuantifiedFormulaManager qfTheory = new CVC4QuantifiedFormulaManager(creator);

    CVC4ArrayFormulaManager arrayTheory = new CVC4ArrayFormulaManager(creator);
    CVC4SLFormulaManager slTheory = new CVC4SLFormulaManager(creator);
    CVC4StringFormulaManager strTheory = new CVC4StringFormulaManager(creator);
    CVC4FormulaManager manager =
        new CVC4FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            fpTheory,
            qfTheory,
            arrayTheory,
            slTheory,
            strTheory);

    return new CVC4SolverContext(creator, manager, pShutdownNotifier, randomSeed);
  }

  @Override
  public String getVersion() {
    return "CVC4 " + CVC4JNI.Configuration_getVersionString();
  }

  @Override
  public void close() {
    if (creator != null) {
      creator.getEnv().delete();
      creator = null;
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC4;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new CVC4TheoremProver(
        getFormulaManager(), creator, shutdownNotifier, randomSeed, pOptions);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC4 does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC4 does not support optimization");
  }
}
