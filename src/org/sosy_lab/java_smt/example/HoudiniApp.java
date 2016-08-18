package org.sosy_lab.java_smt.example;

import com.google.common.collect.ImmutableList;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
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
import org.sosy_lab.java_smt.visitors.FormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;

/**
 * This application executes the inductive-invariant synthesis algorithm
 * called "Houdini" taken from the paper
 * Flanagan and Leino: "Houdini, an Annotation Assistant for ESC/Java".
 *
 * <p>It considers a program manipulating a set X of variables, defined by an
 * initial condition I(X) (given as lemmas) and a transition relation T(X, X').
 * Both I and T are quantifier-free first-order formulas.
 *
 * <p>A lemma F is called inductive with respect to T
 * if it implies itself over the primed variables after the transition:
 *     FORALL X, X' . IMPLIES( AND( F(X), T(X, X') ), F(X'))
 * i.e. in other words, the formula
 *     AND( F(X), T(X, X'), NOT(F(X')) )
 * is unsatisfiable.
 *
 * <p>The Houdini algorithm finds and returns a maximal inductive subset L_I
 * of a given set L of candidate lemmas.
 * It repeatedly checks the conjunction of L for inductiveness and updates L
 * to exclude the lemmas that give rise to counterexamples-to-induction.
 */
public class HoudiniApp {
  private final FormulaManager fmgr;
  private final BooleanFormulaManager bfmgr;
  private final SolverContext context;

  public static void main(String... args) throws Exception {
    LogManager mainLogger = BasicLogManager.create(Configuration.defaultConfiguration());
    for (Solvers solver : Solvers.values()) {
      mainLogger.log(Level.INFO, "using solver", solver);

      // initialize Houdini
      HoudiniApp houdini = new HoudiniApp("--solver.solver=" + solver);

      IntegerFormulaManager ifmgr = houdini.fmgr.getIntegerFormulaManager();

      // create some symbols
      IntegerFormula x = ifmgr.makeVariable("X");
      IntegerFormula xPrimed = ifmgr.makeVariable("X'");
      IntegerFormula one = ifmgr.makeNumber(1);

      // for the transition X'=X+1 the lemma X>1 is valid and X<1 is invalid.
      List<BooleanFormula> lemmas =
          ImmutableList.of(ifmgr.greaterThan(x, one), ifmgr.lessThan(x, one));
      BooleanFormula transition = ifmgr.equal(xPrimed, ifmgr.add(x, one));

      // compute the maximal inductive subset
      List<BooleanFormula> result = houdini.houdini(lemmas, transition);

      mainLogger.log(Level.INFO, "Houdini returned", result);
    }
  }

  public HoudiniApp(String... args) throws Exception {
    Configuration config = Configuration.fromCmdLineArguments(args);
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownManager.create().getNotifier();

    context = SolverContextFactory.createSolverContext(config, logger, notifier);
    fmgr = context.getFormulaManager();
    bfmgr = context.getFormulaManager().getBooleanFormulaManager();
  }

  private BooleanFormula getSelectorVar(int idx) {
    return bfmgr.makeVariable("SEL_" + idx);
  }

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

  public List<BooleanFormula> houdini(List<BooleanFormula> lemmas, BooleanFormula transition)
      throws Exception {
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
