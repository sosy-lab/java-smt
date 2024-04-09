// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.example;

import com.google.common.base.Verify;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

/** Example of a simple user propagator that prohibits variables/expressions to be set to true. */
public class SimpleUserPropagator {

  private SimpleUserPropagator() {}

  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, SolverException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.Z3)) {
      final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();

      testWithBlockedLiterals(context, bmgr, logger);
      testWithBlockedClause(context, bmgr, logger);
      testWithBlockedSubclauses(context, bmgr, logger);

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
      logger.logUserException(Level.INFO, e, "Z3 is not available.");
    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static void testWithBlockedLiterals(
      SolverContext context, BooleanFormulaManager bmgr, LogManager logger)
      throws InterruptedException, SolverException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      // assert "p or q or r or s"
      BooleanFormula p = bmgr.makeVariable("p");
      BooleanFormula q = bmgr.makeVariable("q");
      BooleanFormula r = bmgr.makeVariable("r");
      BooleanFormula s = bmgr.makeVariable("s");
      BooleanFormula clause = bmgr.or(p, q, r, s);
      prover.addConstraint(clause);

      logger.log(
          Level.INFO,
          "========== Checking satisfiability of",
          clause,
          "while blocking " + "all literals ==========");

      // Create user propagator that prohibits variables to be set to true
      MyUserPropagator myUserPropagator = new MyUserPropagator(logger);
      Verify.verify(prover.registerUserPropagator(myUserPropagator));
      myUserPropagator.registerExpression(p);
      myUserPropagator.registerExpression(q);
      myUserPropagator.registerExpression(r);
      myUserPropagator.registerExpression(s);

      // Instance should be UNSAT now due to the user propagator
      boolean isUnsat = prover.isUnsat();
      logger.log(Level.INFO, "Formula", clause, "is", isUnsat ? "UNSAT" : "SAT");
    }
  }

  private static void testWithBlockedClause(
      SolverContext context, BooleanFormulaManager bmgr, LogManager logger)
      throws InterruptedException, SolverException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      // assert "p or q or r or s"
      BooleanFormula p = bmgr.makeVariable("p");
      BooleanFormula q = bmgr.makeVariable("q");
      BooleanFormula r = bmgr.makeVariable("r");
      BooleanFormula s = bmgr.makeVariable("s");
      BooleanFormula clause = bmgr.or(p, q, r, s);
      prover.addConstraint(clause);

      logger.log(
          Level.INFO,
          "========== Checking satisfiability of",
          clause,
          "while blocking " + "the full clause ==========");

      // Create user propagator that prohibits the full clause to be set to true.
      MyUserPropagator myUserPropagator = new MyUserPropagator(logger);
      Verify.verify(prover.registerUserPropagator(myUserPropagator));
      myUserPropagator.registerExpression(clause);

      // Instance should be UNSAT now due to the user propagator
      boolean isUnsat = prover.isUnsat();
      logger.log(Level.INFO, "Formula", clause, "is", isUnsat ? "UNSAT" : "SAT");
    }
  }

  private static void testWithBlockedSubclauses(
      SolverContext context, BooleanFormulaManager bmgr, LogManager logger)
      throws InterruptedException, SolverException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      // assert "p or q or r or s"
      BooleanFormula p = bmgr.makeVariable("p");
      BooleanFormula q = bmgr.makeVariable("q");
      BooleanFormula r = bmgr.makeVariable("r");
      BooleanFormula s = bmgr.makeVariable("s");
      BooleanFormula clause = bmgr.or(p, q, r, s);
      BooleanFormula subclause1 = bmgr.or(p, q);
      BooleanFormula subclause2 = bmgr.or(r, s);
      prover.addConstraint(clause);

      logger.log(
          Level.INFO,
          "========== Checking satisfiability of",
          clause,
          "while blocking " + "the subclauses",
          subclause1,
          "and",
          subclause2,
          "==========");

      // Create user propagator that prohibits (sub)clauses to be set to true.
      // Note that the subclauses are not directly asserted in the original input formula.
      MyUserPropagator myUserPropagator = new MyUserPropagator(logger);
      Verify.verify(prover.registerUserPropagator(myUserPropagator));
      myUserPropagator.registerExpression(subclause1);
      myUserPropagator.registerExpression(subclause2);

      // Instance should be UNSAT now due to the user propagator
      boolean isUnsat = prover.isUnsat();
      logger.log(Level.INFO, "Formula", clause, "is", isUnsat ? "UNSAT" : "SAT");
    }
  }

  /** This user propagator will raise a conflict whenever a registered expression is set to true. */
  private static class MyUserPropagator extends AbstractUserPropagator {

    private final List<BooleanFormula> disabledExpressions = new ArrayList<>();
    private final LogManager logger;

    MyUserPropagator(LogManager logger) {
      this.logger = logger;
    }

    @Override
    public void onPush() {
      logger.log(Level.INFO, "Solver pushed");
    }

    @Override
    public void onPop(int numPoppedLevels) {
      logger.log(Level.INFO, "Solver popped", numPoppedLevels, "levels");
    }

    @Override
    public void onKnownValue(BooleanFormula expr, boolean value) {
      logger.log(Level.INFO, "Solver assigned", expr, "to", value);
      if (value && disabledExpressions.contains(expr)) {
        logger.log(Level.INFO, "User propagator raised conflict on", expr);
        getBackend().propagateConflict(new BooleanFormula[] {expr});
      }
    }

    @Override
    public void onDecision(BooleanFormula expr, boolean value) {
      // NOTE 1: This part just serves to show the ability to affect solver decision.
      // In this case, we force the solver to run into conflicts as early as possible.
      // NOTE 2: The same code could be executed in `onKnownValue` to influence the next(!)
      // decision the solver would make.
      for (BooleanFormula disExpr : disabledExpressions) {
        final boolean decisionValue = true;
        if (getBackend().propagateNextDecision(disExpr, Optional.of(decisionValue))) {
          // The above call returns "true" if the provided literal is yet undecided, otherwise
          // false.
          logger.log(
              Level.INFO,
              String.format(
                  "User propagator overwrites decision from '%s = %s' to '%s = %s'",
                  expr, value, disExpr, decisionValue));
          break;
        }
      }
    }

    @Override
    public void initializeWithBackend(PropagatorBackend backend) {
      super.initializeWithBackend(backend);
      // Enable callbacks
      backend.notifyOnKnownValue();
      backend.notifyOnDecision();
    }

    @Override
    public void registerExpression(BooleanFormula theoryExpr) {
      disabledExpressions.add(theoryExpr);
      super.registerExpression(theoryExpr);
    }
  }
}
