// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.BOOLECTOR;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.PRINCESS;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.SMTINTERPOL;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.YICES2;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment.AllSatCallback;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This example shows different ways to get all satisfiable models for a given set of constraints.
 */
@SuppressWarnings("unused")
public class AllSatExample {

  private static final ImmutableSet<Solvers> SOLVERS_WITH_INTEGERS =
      ImmutableSet.of(MATHSAT5, SMTINTERPOL, Z3, PRINCESS, CVC4, YICES2);
  private static final ImmutableSet<Solvers> SOLVERS_WITH_BITVECTORS =
      ImmutableSet.of(MATHSAT5, Z3, PRINCESS, BOOLECTOR, CVC4);

  private BooleanFormulaManager bfmgr;
  private IntegerFormulaManager ifmgr;
  private BitvectorFormulaManager bvfmgr;
  private final ProverEnvironment prover;
  private final SolverContext context;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    for (Solvers solver : Solvers.values()) {
      try (SolverContext context =
              SolverContextFactory.createSolverContext(config, logger, notifier, solver);
          ProverEnvironment prover =
              context.newProverEnvironment(
                  ProverOptions.GENERATE_MODELS, ProverOptions.GENERATE_ALL_SAT)) {
        logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

        AllSatExample ase = new AllSatExample(context, prover);

        prover.push();
        logger.log(Level.INFO, ase.allSatBooleans1());
        prover.pop();

        prover.push();
        logger.log(Level.INFO, ase.allSatBooleans2());
        prover.pop();

        if (SOLVERS_WITH_INTEGERS.contains(solver)) {
          prover.push();
          logger.log(Level.INFO, ase.allSatIntegers());
          prover.pop();

          prover.push();
          logger.log(Level.INFO, ase.allSatIntegers2());
          prover.pop();
        }

        if (SOLVERS_WITH_BITVECTORS.contains(solver)) {
          prover.push();
          logger.log(Level.INFO, ase.allSatBitvectors());
          prover.pop();
        }

      } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

        // on some machines we support only some solvers,
        // thus we can ignore these errors.
        logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

      } catch (UnsupportedOperationException e) {
        logger.logUserException(Level.INFO, e, e.getMessage());
      }
    }
  }

  public AllSatExample(SolverContext pContext, ProverEnvironment pProver) {
    prover = pProver;
    context = pContext;
  }

  /** For boolean symbols we can directly use the method {@link ProverEnvironment#allSat}. */
  private List<List<BooleanFormula>> allSatBooleans1()
      throws InterruptedException, SolverException {
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();

    // formula (p --> q) with 3 models
    BooleanFormula p = bfmgr.makeVariable("p");
    BooleanFormula q = bfmgr.makeVariable("q");

    prover.addConstraint(bfmgr.implication(p, q));

    return prover.allSat(
        new AllSatCallback<>() {

          private final List<List<BooleanFormula>> models = new ArrayList<>();

          @Override
          public void apply(List<BooleanFormula> pModel) {
            models.add(pModel);
          }

          @Override
          public List<List<BooleanFormula>> getResult() {
            return models;
          }
        },
        ImmutableList.of(q, p));
  }

  /** For boolean symbols we can also ask the model directly for evaluations of symbols. */
  private List<List<ValueAssignment>> allSatBooleans2()
      throws InterruptedException, SolverException {
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();

    // formula (p --> q) with 3 models
    BooleanFormula p = bfmgr.makeVariable("p");
    BooleanFormula q = bfmgr.makeVariable("q");

    prover.addConstraint(bfmgr.implication(p, q));
    List<List<ValueAssignment>> models = new ArrayList<>();

    // loop over all possible models
    while (!prover.isUnsat()) {
      models.add(prover.getModelAssignments());
      try (Model model = prover.getModel()) {

        List<BooleanFormula> assignments = new ArrayList<>();
        Boolean valueQ = model.evaluate(q);
        // an unbounded result is null
        if (valueQ != null) {
          assignments.add(bfmgr.equivalence(q, bfmgr.makeBoolean(valueQ)));
        }
        Boolean valueP = model.evaluate(p);
        // an unbounded result is null
        if (valueP != null) {
          assignments.add(bfmgr.equivalence(p, bfmgr.makeBoolean(valueP)));
        }

        // prevent next model from using the same assignment as a previous model
        prover.addConstraint(bfmgr.not(bfmgr.and(assignments)));
      }
    }

    return models;
  }

  /**
   * For integer formulas, we can implement the allsat-loop and collect all models when iterating.
   */
  private List<List<ValueAssignment>> allSatIntegers()
      throws InterruptedException, SolverException {
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();
    ifmgr = context.getFormulaManager().getIntegerFormulaManager();

    // formula ((1 <= a <= 10) && (1 <= b <= 10) && (a >= 2 * b)) with 25 models
    IntegerFormula a = ifmgr.makeVariable("a");
    IntegerFormula b = ifmgr.makeVariable("b");

    prover.addConstraint(ifmgr.lessOrEquals(num(1), a));
    prover.addConstraint(ifmgr.lessOrEquals(a, num(10)));
    prover.addConstraint(ifmgr.lessOrEquals(num(1), b));
    prover.addConstraint(ifmgr.lessOrEquals(b, num(10)));
    prover.addConstraint(ifmgr.greaterOrEquals(a, ifmgr.multiply(num(2), b)));

    List<List<ValueAssignment>> models = new ArrayList<>();

    // loop over all possible models for "1<=a<=10 AND 1<=b<=10 AND a==2*b"
    while (!prover.isUnsat()) {
      models.add(prover.getModelAssignments());
      try (Model model = prover.getModel()) {

        // convert model into formula, assuming we know all symbols and know they are integers
        BooleanFormula modelAsFormula =
            bfmgr.and(
                ifmgr.equal(a, num(model.evaluate(a))), ifmgr.equal(b, num(model.evaluate(b))));

        // prevent next model from using the same assignment as a previous model
        prover.addConstraint(bfmgr.not(modelAsFormula));
      }
    }

    return models;
  }

  /**
   * For integer formulas, we can implement the allsat-loop and collect all models when iterating.
   */
  private List<List<ValueAssignment>> allSatIntegers2()
      throws InterruptedException, SolverException {
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();
    ifmgr = context.getFormulaManager().getIntegerFormulaManager();

    // formula ((1 <= a <= 3) && (0 == b) && (p == q)) with 6 models
    IntegerFormula a = ifmgr.makeVariable("a");
    IntegerFormula b = ifmgr.makeVariable("b");
    BooleanFormula p = bfmgr.makeVariable("p");
    BooleanFormula q = bfmgr.makeVariable("q");

    prover.addConstraint(ifmgr.lessOrEquals(num(1), a));
    prover.addConstraint(ifmgr.equal(num(0), b));
    prover.addConstraint(ifmgr.lessOrEquals(a, num(3)));
    prover.addConstraint(bfmgr.equivalence(p, q));

    List<List<ValueAssignment>> models = new ArrayList<>();

    // loop over all possible models for "1<=a<=3 AND p=q"
    while (!prover.isUnsat()) {
      final ImmutableList<ValueAssignment> modelAssignments = prover.getModelAssignments();

      models.add(modelAssignments);

      final List<BooleanFormula> modelAssignmentsAsFormulas = new ArrayList<>();
      for (ValueAssignment va : modelAssignments) {
        modelAssignmentsAsFormulas.add(va.getAssignmentAsFormula());
      }

      // prevent next model from using the same assignment as a previous model
      prover.addConstraint(bfmgr.not(bfmgr.and(modelAssignmentsAsFormulas)));
    }

    return models;
  }

  private IntegerFormula num(int number) {
    return ifmgr.makeNumber(number);
  }

  private IntegerFormula num(BigInteger number) {
    return ifmgr.makeNumber(number);
  }

  /**
   * For bitvector formulas, we can implement the allsat-loop and collect all models when iterating.
   */
  private List<List<ValueAssignment>> allSatBitvectors()
      throws InterruptedException, SolverException {
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();
    bvfmgr = context.getFormulaManager().getBitvectorFormulaManager();

    // formula ((1 <= a <= 3) && (0 == b) && (p == q)) with 6 models
    final int bitsize = 4;
    BitvectorFormula a = bvfmgr.makeVariable(bitsize, "c");
    BitvectorFormula b = bvfmgr.makeVariable(bitsize, "d");
    BooleanFormula p = bfmgr.makeVariable("r");
    BooleanFormula q = bfmgr.makeVariable("s");

    prover.addConstraint(bvfmgr.lessOrEquals(bv(bitsize, 1), a, true));
    prover.addConstraint(bvfmgr.equal(bv(bitsize, 0), b));
    prover.addConstraint(bvfmgr.lessOrEquals(a, bv(bitsize, 3), true));
    prover.addConstraint(bfmgr.equivalence(p, q));

    List<List<ValueAssignment>> models = new ArrayList<>();

    // loop over all possible models for "1<=a<=3 AND p=q"
    while (!prover.isUnsat()) {
      final ImmutableList<ValueAssignment> modelAssignments = prover.getModelAssignments();

      models.add(modelAssignments);

      final List<BooleanFormula> modelAssignmentsAsFormulas = new ArrayList<>();
      for (ValueAssignment va : modelAssignments) {
        modelAssignmentsAsFormulas.add(va.getAssignmentAsFormula());
      }

      // prevent next model from using the same assignment as a previous model
      prover.addConstraint(bfmgr.not(bfmgr.and(modelAssignmentsAsFormulas)));
    }

    return models;
  }

  private BitvectorFormula bv(int bitsize, int number) {
    return bvfmgr.makeBitvector(bitsize, number);
  }
}
