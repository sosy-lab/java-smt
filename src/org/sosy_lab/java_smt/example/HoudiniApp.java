package org.sosy_lab.java_smt.example;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;

/**
 * This application executes the inductive-invariant synthesis algorithm called "Houdini" taken from
 * the paper Flanagan and Leino: "Houdini, an Annotation Assistant for ESC/Java".
 *
 * <p>It considers a program manipulating a set X of variables, defined by an initial condition I(X)
 * (given as lemmas) and a transition relation T(X, X'). Both I and T are quantifier-free
 * first-order formulas.
 *
 * <p>A lemma F is called inductive with respect to T if it implies itself over the primed variables
 * after the transition: FORALL X, X' . IMPLIES( AND( F(X), T(X, X') ), F(X')) i.e. in other words,
 * the formula AND( F(X), T(X, X'), NOT(F(X')) ) is unsatisfiable.
 *
 * <p>The Houdini algorithm finds and returns a maximal inductive subset L_I of a given set L of
 * candidate lemmas. It repeatedly checks the conjunction of L for inductiveness and updates L to
 * exclude the lemmas that give rise to counterexamples-to-induction.
 */
public class HoudiniApp {

  private final FormulaManager fmgr;
  private final BooleanFormulaManager bfmgr;
  private final SolverContext context;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // this example executes the Houdini algorithm for all available solvers
    for (Solvers solver : Solvers.values()) {
      logger.log(Level.INFO, "using solver", solver);

      // create the solver context, which includes all necessary parts for building, manipulating,
      // and solving formulas.
      try (SolverContext solverContext =
          SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

        // initialize Houdini
        HoudiniApp houdini = new HoudiniApp(solverContext);

        IntegerFormulaManager ifmgr = solverContext.getFormulaManager().getIntegerFormulaManager();

        // create some symbols for the example
        IntegerFormula x = ifmgr.makeVariable("X");
        IntegerFormula xPrimed = ifmgr.makeVariable("X'");
        IntegerFormula one = ifmgr.makeNumber(1);

        // create boolean formulas for the example,
        // for the transition X'=X+1 the lemma X>1 is valid and X<1 is invalid.
        List<BooleanFormula> lemmas =
            ImmutableList.of(ifmgr.greaterThan(x, one), ifmgr.lessThan(x, one));
        BooleanFormula transition = ifmgr.equal(xPrimed, ifmgr.add(x, one));

        // use Houdini and compute the maximal inductive subset
        List<BooleanFormula> result = houdini.houdini(lemmas, transition);

        logger.log(Level.INFO, "Houdini returned", result);

      } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

        // on some machines we support only some solvers,
        // e.g. Windows does not have Mathsat by default.
        // Thus we can ignore these errors.
        logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

      } catch (UnsupportedOperationException e) {
        logger.logUserException(Level.INFO, e, e.getMessage());
      }
    }
  }

  public HoudiniApp(SolverContext solverContext) {
    context = solverContext;
    fmgr = context.getFormulaManager();
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();
  }

  /** create a temporary symbol using the given index. */
  private BooleanFormula getSelectorVar(int idx) {
    return bfmgr.makeVariable("SEL_" + idx);
  }

  /** traverse the formula and replace all symbols in the formula with their primed version. */
  private BooleanFormula prime(BooleanFormula input) {
    return fmgr.transformRecursively(
        input,
        new FormulaTransformationVisitor(fmgr) {

          @Override
          public Formula visitFreeVariable(Formula f, String name) {
            return fmgr.makeVariable(fmgr.getFormulaType(f), name + "'");
          }
        });
  }

  /**
   * execute the Houdini algorithm to get the maximal inductive subset L_I for the given lemmas and
   * the transition.
   */
  public List<BooleanFormula> houdini(List<BooleanFormula> lemmas, BooleanFormula transition)
      throws SolverException, InterruptedException {
    List<BooleanFormula> annotated = new ArrayList<>();
    List<BooleanFormula> annotatedPrimes = new ArrayList<>();
    Map<Integer, BooleanFormula> indexed = new HashMap<>();

    for (int i = 0; i < lemmas.size(); i++) {
      BooleanFormula lemma = lemmas.get(i);
      BooleanFormula primed = prime(lemma);

      annotated.add(bfmgr.or(getSelectorVar(i), lemma));
      annotatedPrimes.add(bfmgr.or(getSelectorVar(i), primed));
      indexed.put(i, lemma);
    }

    // create a prover environment for solving the formulas and receiving a model
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(transition);
      prover.addConstraint(bfmgr.and(annotated));
      prover.addConstraint(bfmgr.not(bfmgr.and(annotatedPrimes)));

      while (!prover.isUnsat()) {
        try (Model m = prover.getModel()) {
          for (int i = 0; i < annotatedPrimes.size(); i++) {
            BooleanFormula annotatedPrime = annotatedPrimes.get(i);
            if (!m.evaluate(annotatedPrime)) {
              prover.addConstraint(getSelectorVar(i));
              indexed.remove(i);
            }
          }
        }
      }
    }
    return new ArrayList<>(indexed.values());
  }
}
