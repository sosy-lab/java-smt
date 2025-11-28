/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.example;

import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.List;
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
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class IndependentInterpolation {

  public static void main(String[] args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    Solvers solver = Solvers.Z3;

    try (SolverContext context =
             SolverContextFactory.createSolverContext(config, logger, notifier, solver);
         InterpolatingProverEnvironment<?> prover =
             context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      BooleanFormulaManager bmgr = context.getFormulaManager().getBooleanFormulaManager();
      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      // example
      prover.push();
      interpolateExample(prover, bmgr, imgr, logger);
      prover.pop();

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  private static <T> void interpolateExample(
      InterpolatingProverEnvironment<T> prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    // A: x = 1 && x = y
    // B: y = z && z = 2
    // -> y = 1, y != 2


    // create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula two = imgr.makeNumber(2);

    // create and assert some formulas
    // instead of 'named' formulas, we return a 'handle' (of generic type T)

    T ip0 =
        prover.push(
            bmgr.and(
                imgr.equal(y, z), imgr.equal(z, two)
            ));
    T ip1 = prover.push(bmgr.and(imgr.equal(x, one), imgr.equal(y, x)));


    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.log(Level.INFO, "Interpolants are:", itp);
  }

  private static <T> void interpolateExample2(
      InterpolatingProverEnvironment<T> prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    // A: x > 0 && y = x + 1
    // B: y < 0
    // -> y > 0

    // create some variables
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula zero = imgr.makeNumber(0);

    T ip0 =
        prover.push(imgr.lessThan(y, zero));
    T ip1 = prover.push(bmgr.and(imgr.greaterThan(x, zero), imgr.equal(y, imgr.add(x, one))));


    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "The example for interpolation should be UNSAT");

    BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip1));
    logger.log(Level.INFO, "Interpolants are:", itp);
  }

  private static <T> void interpolateExample3(
      InterpolatingProverEnvironment<T> prover,
      BooleanFormulaManager bmgr,
      IntegerFormulaManager imgr,
      LogManager logger)
      throws InterruptedException, SolverException {

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula thousand = imgr.makeNumber(1000);

    IntegerFormula i3 = imgr.makeVariable("i3");
    IntegerFormula i4 = imgr.makeVariable("i4");

    BooleanFormula A = imgr.equal(i3, zero);
    BooleanFormula B = bmgr.and(imgr.lessThan(i3, thousand), imgr.equal(i4, imgr.add(i3, one)));
    BooleanFormula C = imgr.greaterThan(i4, thousand);

    T TA = prover.push(A);
    T TB = prover.push(B);
    T TC = prover.push(C);

    assertThat(prover).isUnsatisfiable();

    List<BooleanFormula> itpSeq = prover.getSeqInterpolants0(ImmutableList.of(TA, TB, TC));

    BooleanFormula itp1 = prover.getInterpolant(ImmutableList.of(TA));
    BooleanFormula itp2 = prover.getInterpolant(ImmutableList.of(TA, TB));
  }
}


