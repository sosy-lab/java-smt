// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/** Minimal LeanSMT example covering SAT/UNSAT checks and model term retrieval. */
public final class LeanSmtBasicExample {

  private LeanSmtBasicExample() {}

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.LEANSMT);
        ProverEnvironment prover =
            context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");

      // SAT part
      BooleanFormula satConstraint =
          bmgr.and(imgr.greaterThan(x, imgr.makeNumber(0)), imgr.lessThan(x, imgr.makeNumber(4)));
      prover.push(satConstraint);
      boolean satIsUnsat = prover.isUnsat();
      System.out.println("LeanSMT SAT check (expected false): " + satIsUnsat);

      try (Model model = prover.getModel()) {
        // Use term-level model API, which is currently robust for LeanSMT.
        System.out.println("LeanSMT model assignments: " + model.asList().size());
        System.out.println("LeanSMT eval(x) term: " + model.eval(x));
      }

      // UNSAT part
      BooleanFormula unsatConstraint =
          bmgr.and(imgr.equal(y, imgr.makeNumber(1)), imgr.equal(y, imgr.makeNumber(2)));
      prover.push(unsatConstraint);
      boolean unsat = prover.isUnsat();
      System.out.println("LeanSMT UNSAT check (expected true): " + unsat);
    }
  }
}
