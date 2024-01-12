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

package org.sosy_lab.java_smt.example;

import static com.google.common.base.Verify.verify;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import com.google.common.base.Verify;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

/**
 * Example of a simple user propagator that prohibits variables to be set to true.
 */
public class SimpleUserPropagator {

  public static void main (String[] args) throws InvalidConfigurationException,
                                                 InterruptedException, SolverException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context = SolverContextFactory.createSolverContext(config, logger, notifier,
            Solvers.Z3);
         ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      final BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();

      // assert "p or q"
      BooleanFormula p = bmgr.makeVariable("p");
      BooleanFormula q = bmgr.makeVariable("q");
      BooleanFormula p_or_q = bmgr.or(p, q);
      prover.addConstraint(p_or_q);

      // Create user propagator that prohibits variables to be set to true
      MyUserPropagator myUserPropagator = new MyUserPropagator(bmgr, logger);
      Verify.verify(prover.registerUserPropagator(myUserPropagator));
      myUserPropagator.registerExpression(p);
      myUserPropagator.registerExpression(q);

      // Instance should be UNSAT now due to the user propagator
      boolean isUnsat = prover.isUnsat();
      logger.log(Level.INFO, "Formula", p_or_q, "is", isUnsat ? "UNSAT" : "SAT");

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
      logger.logUserException(Level.INFO, e, "Z3 is not available.");
    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }

  }

  /**
   * This user propagator will raise a conflict whenever a variable is set to true.
   */
  private static class MyUserPropagator extends AbstractUserPropagator {

    private final List<BooleanFormula> disabledLiterals = new ArrayList<>();
    private final BooleanFormulaManager bmgr;
    private final LogManager logger;

    public MyUserPropagator(BooleanFormulaManager bmgr, LogManager logger) {
      this.bmgr = bmgr;
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
    public void onKnownValue(BooleanFormula expr, BooleanFormula val) {
      logger.log(Level.INFO, "Solver assigned", expr, "to", val);
      if (disabledLiterals.contains(expr) && bmgr.isTrue(val)) {
        logger.log(Level.INFO, "User propagator raised conflict on", expr);
        backend.propagateConflict(new BooleanFormula[] { expr });
      }
    }

    @Override
    public void initialize() {
      // Enable "onKnownValue" callback
      backend.notifyOnKnownValue();
    }

    @Override
    public void registerExpression(BooleanFormula theoryExpr) {
      disabledLiterals.add(theoryExpr);
      super.registerExpression(theoryExpr);
    }
  }
}
