package org.sosy_lab.java_smt.example;

import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment.AllSatCallback;
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

  private final BooleanFormulaManager bfmgr;
  private final IntegerFormulaManager ifmgr;
  private final ProverEnvironment prover;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    for (Solvers solver : Solvers.values()) {
      System.out.println("\nUsing solver " + solver);
      try (SolverContext context =
              SolverContextFactory.createSolverContext(config, logger, notifier, solver);
          ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

        AllSatExample ase = new AllSatExample(context, prover);

        prover.push();
        System.out.println(ase.allSatBooleans1());
        prover.pop();

        prover.push();
        System.out.println(ase.allSatBooleans2());
        prover.pop();

        prover.push();
        System.out.println(ase.allSatIntegers());
        prover.pop();
      }
    }
  }

  public AllSatExample(SolverContext pContext, ProverEnvironment pProver) {
    bfmgr = pContext.getFormulaManager().getBooleanFormulaManager();
    ifmgr = pContext.getFormulaManager().getIntegerFormulaManager();
    prover = pProver;
  }

  /** For boolean symbols we can directly use the method {@link ProverEnvironment#allSat}. */
  private List<List<BooleanFormula>> allSatBooleans1()
      throws InterruptedException, SolverException {

    BooleanFormula p = bfmgr.makeVariable("p");
    BooleanFormula q = bfmgr.makeVariable("q");

    prover.addConstraint(bfmgr.implication(p, q));

    return prover.allSat(
        new AllSatCallback<List<List<BooleanFormula>>>() {

          List<List<BooleanFormula>> models = new ArrayList<>();

          @Override
          public void apply(List<BooleanFormula> pModel) {
            models.add(pModel);
          }

          @Override
          public List<List<BooleanFormula>> getResult() {
            return models;
          }
        },
        Lists.newArrayList(q, p));
  }

  /** For boolean symbols we can also ask the model directly for evaluations of symbols. */
  private List<List<ValueAssignment>> allSatBooleans2()
      throws InterruptedException, SolverException {

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

    IntegerFormula a = ifmgr.makeVariable("a");
    IntegerFormula b = ifmgr.makeVariable("b");

    prover.addConstraint(ifmgr.lessOrEquals(num(1), a));
    prover.addConstraint(ifmgr.lessOrEquals(a, num(10)));
    prover.addConstraint(ifmgr.lessOrEquals(num(1), b));
    prover.addConstraint(ifmgr.lessOrEquals(b, num(10)));
    prover.addConstraint(ifmgr.greaterOrEquals(a, ifmgr.multiply(num(2), b)));

    List<List<ValueAssignment>> models = new ArrayList<>();

    // loop over all possible models
    while (!prover.isUnsat()) {
      models.add(prover.getModelAssignments());
      try (Model model = prover.getModel()) {

        // convert model into formula
        BooleanFormula modelAsFormula =
            bfmgr.and(
                ifmgr.equal(a, num(model.evaluate(a))), ifmgr.equal(b, num(model.evaluate(b))));

        // prevent next model from using the same assignment as a previous model
        prover.addConstraint(bfmgr.not(modelAsFormula));
      }
    }

    return models;
  }

  private IntegerFormula num(int number) {
    return ifmgr.makeNumber(number);
  }

  private IntegerFormula num(BigInteger number) {
    return ifmgr.makeNumber(number);
  }
}
