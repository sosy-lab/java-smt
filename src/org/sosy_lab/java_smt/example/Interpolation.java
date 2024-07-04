// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolationPoint;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

/** Examples for Craig/sequential/tree interpolation. */
public class Interpolation {

  private Interpolation() {
    // never called
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {

    // set up a basic environment
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // choose solver
    Solvers solver = Solvers.SMTINTERPOL; // works for all interpolation strategies

    // setup context
    try (SolverContext context =
            SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        InterpolatingProverEnvironment<?> prover =
            context.newProverEnvironmentWithInterpolation()) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      IntegerFormulaManager imgr = context.getFormulaManager().getIntegerFormulaManager();

      // example
      prover.push();
      interpolateExample(prover, imgr, logger);
      prover.pop();

      // and another example
      prover.push();
      interpolateProgramTrace(prover, imgr, logger);
      prover.pop();

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  /**
   * Example taken from SMTInterpol, <a
   * href="http://ultimate.informatik.uni-freiburg.de/smtinterpol/interpolation.smt2">example as
   * SMT-LIB</a>:
   *
   * <pre>
   * (set-option :print-success false)
   * (set-option :produce-proofs true)
   * (set-logic QF_LIA)
   * (declare-fun x () Int)
   * (declare-fun y () Int)
   * (assert (! (> x y) :named IP_0))
   * (assert (! (= x 0) :named IP_1))
   * (assert (! (> y 0) :named IP_2))
   * (check-sat)
   * (get-interpolants IP_0 IP_1 IP_2)       // example 1 (1a and 1b)
   * (get-interpolants IP_1 (and IP_0 IP_2)) // example 2 (2a and 2b)
   * (exit)
   * </pre>
   */
  private static <T> void interpolateExample(
      InterpolatingProverEnvironment<T> prover, IntegerFormulaManager imgr, LogManager logger)
      throws InterruptedException, SolverException {

    // create some variables.
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula zero = imgr.makeNumber(0);

    // create and assert some formulas.
    // instead of 'named' formulas, we return a 'handle' (of generic type T)
    InterpolationPoint<T> ip0 = prover.addConstraint(imgr.greaterThan(x, y));
    InterpolationPoint<T> ip1 = prover.addConstraint(imgr.equal(x, zero));
    InterpolationPoint<T> ip2 = prover.addConstraint(imgr.greaterThan(y, zero));

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "the example for interpolation should be UNSAT");

    List<BooleanFormula> itps;

    {
      // example 1a :
      // get a sequence of interpolants for three formulas: (get-interpolants IP_0 IP_1 IP_2).
      itps = prover.getSeqInterpolants0(ImmutableList.of(ip0, ip1, ip2));
      logger.log(Level.INFO, "1a :: Interpolants for [{ip0},{ip1},{ip2}] are:", itps);
    }

    {
      // example 1b :
      // alternative solution ... with more code and partitioned formulas.
      Set<InterpolationPoint<T>> partition0 = ImmutableSet.of(ip0);
      Set<InterpolationPoint<T>> partition1 = ImmutableSet.of(ip1);
      Set<InterpolationPoint<T>> partition2 = ImmutableSet.of(ip2);
      itps = prover.getSeqInterpolants(ImmutableList.of(partition0, partition1, partition2));
      logger.log(Level.INFO, "1b :: Interpolants for [{ip0},{ip1},{ip2}] are:", itps);
    }

    {
      // example 2a :
      // get a sequence of interpolants for two formulas: (get-interpolants IP_1 (and IP_0 IP_2)).
      Set<InterpolationPoint<T>> partition3 = ImmutableSet.of(ip0);
      Set<InterpolationPoint<T>> partition4 = ImmutableSet.of(ip1, ip2);
      itps = prover.getSeqInterpolants(ImmutableList.of(partition3, partition4));
      logger.log(Level.INFO, "2a :: Interpolants for [{ip0},{ip1,ip2}] are:", itps);
    }

    {
      // example 2b :
      // alternative solution, works when there are exactly two (!) groups of formulas.
      // only one part is given as parameter, the rest is taken from the already asserted formulas.
      BooleanFormula itp = prover.getInterpolant(ImmutableList.of(ip0));
      logger.log(Level.INFO, "2b :: Interpolants for [{ip0},{ip1,ip2}] are:", itp);
    }
  }

  /**
   * Example for encoding a program path and computing interpolants along the path. Taken from <a
   * href="http://satsmt2014.forsyte.at/files/2014/01/interpolation_philipp.pdf">slides</a> from
   * Philipp Rümmer.
   *
   * <p>Example trace of a program:
   *
   * <pre>
   * i=0
   * k=j
   * assume (i<50)
   * i++
   * k++
   * assume (i>=50)
   * assume (j==0)
   * assume (k<50)
   * </pre>
   */
  private static <T> void interpolateProgramTrace(
      InterpolatingProverEnvironment<T> prover, IntegerFormulaManager imgr, LogManager logger)
      throws InterruptedException, SolverException {

    // create some variables.
    // primed variable needed for 'self-assignments', alternatively use SSA-indices.
    IntegerFormula i = imgr.makeVariable("i");
    IntegerFormula i1 = imgr.makeVariable("i'");
    IntegerFormula j = imgr.makeVariable("j");
    IntegerFormula k = imgr.makeVariable("k");
    IntegerFormula k1 = imgr.makeVariable("k'");
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula fifty = imgr.makeNumber(50);

    // create and assert some formulas.
    List<BooleanFormula> programTrace =
        ImmutableList.of(
            imgr.equal(i, zero),
            imgr.equal(k, j),
            imgr.lessThan(i, fifty),
            imgr.equal(i1, imgr.add(i, one)),
            imgr.equal(k1, imgr.add(k, one)),
            imgr.greaterOrEquals(i1, fifty),
            imgr.equal(j, zero),
            imgr.lessThan(k1, fifty));

    // assert all formulas in the prover
    List<InterpolationPoint<T>> handles = new ArrayList<>();
    for (BooleanFormula step : programTrace) {
      handles.add(prover.addConstraint(step));
    }

    // check for satisfiability
    boolean unsat = prover.isUnsat();
    Preconditions.checkState(unsat, "the example for interpolation should be UNSAT");

    // get a sequence of interpolants for the program trace.
    List<BooleanFormula> itps = prover.getSeqInterpolants0(handles);
    logger.log(Level.INFO, "Interpolants for the program trace are:", itps);
  }
}
