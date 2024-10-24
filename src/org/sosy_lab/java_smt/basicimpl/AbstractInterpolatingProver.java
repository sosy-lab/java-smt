/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import java.text.Normalizer.Form;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Collectors;
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
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;

public abstract class AbstractInterpolatingProver<TFormulaInfo extends Formula, TType>
    extends AbstractProverWithAllSat<TFormulaInfo>
    implements InterpolatingProverEnvironment<TFormulaInfo> {

  private final FormulaCreator<TFormulaInfo, TType, ?, ?> creator;
  private final FormulaManager mgr;
  private final QuantifiedFormulaManager qfmgr;
  private final BooleanFormulaManager bmgr;
  private final UFManager ufmgr;

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      BooleanFormulaManager pBmgr,
      QuantifiedFormulaManager pQfmgr,
      ShutdownNotifier pShutdownNotifier,
      FormulaCreator<?, ?, ?, ?> pCreator,
      UFManager pUfmgr) {
    super(pOptions, pMgr, pBmgr, pQfmgr, pShutdownNotifier);
    mgr = pMgr;
    bmgr = pBmgr;
    creator = (FormulaCreator<TFormulaInfo, TType, ?, ?>) pCreator;
    qfmgr = pQfmgr;
    ufmgr = pUfmgr;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
      throws InterruptedException, SolverException {
    checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    final ImmutableCollection<Formula> assertedFormulas =
        ImmutableList.copyOf(getAssertedFormulas());
    final Collection<BooleanFormula> formulasOfA =
        (List<BooleanFormula>) ImmutableList.copyOf(pFormulasOfA);
    final ImmutableCollection<Formula> formulasOfB = assertedFormulas.stream()
        .filter(formula -> !formulasOfA.contains(formula))
        .collect(ImmutableList.toImmutableList());

    return getModelBasedInterpolation(formulasOfA, formulasOfB);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<TFormulaInfo>> partitionedFormulas,
      int[] startOfSubTree) {
    return List.of();
  }

  private BooleanFormula getModelBasedInterpolation(
      Collection<BooleanFormula> formulasA, Collection<Formula> formulasB)
      throws InterruptedException, SolverException {

    BooleanFormula interpolant = null;



    // TODO: Refactor. Conjunction?
    BooleanFormula A = bmgr.and(formulasA);
    BooleanFormula B = null;

    for (Formula formula : formulasA) {
      A = (BooleanFormula) formula;
    }

    for (Formula formula : formulasB) {
      B = (BooleanFormula) formula;
    }


    // free arithmetic variables A and B
    List<Formula> varsOfA = formulasA.stream()
        .flatMap(formula -> mgr.extractVariablesAndUFs(formula).values().stream())
        .collect(Collectors.toList());

    List<Formula> varsOfB = formulasB.stream()
        .flatMap(formula -> mgr.extractVariablesAndUFs(formula).values().stream())
        .collect(Collectors.toList());


    // shared variables between A and B
    ImmutableSet<Formula> setOfVarsA = ImmutableSet.copyOf(varsOfA);
    ImmutableSet<Formula> setOfVarsB = ImmutableSet.copyOf(varsOfB);

    ImmutableList<Formula> sharedVariables =
        Sets.intersection(setOfVarsA, setOfVarsB).immutableCopy().asList();
    System.out.println("shared variables: " + sharedVariables);

    BooleanFormula itp = ufmgr.declareAndCallUF(sharedVariables.toString(),
        FormulaType.BooleanType, sharedVariables);
    System.out.println("itp: " + itp);


    // left: A -> I is UNSAT
    BooleanFormula bodyLeft = bmgr.and(bmgr.implication(A, itp));
    BooleanFormula left = qfmgr.forall(varsOfA, bodyLeft);
    System.out.println("left: " + left);

    // right: I -> not B is UNSAT
    BooleanFormula bodyRight = bmgr.and(bmgr.implication(itp, bmgr.not(B)));
    BooleanFormula right = qfmgr.forall(varsOfB, bodyRight);
    System.out.println("right: " + right);


    // solve left and right
    pop();
    System.out.println("left and right: \n" + bmgr.and(left, right)); // prettyprinter
    push(bmgr.and(left, right));

    if (!isUnsat()) {
      try (Model answer = getModel()) {
        interpolant = answer.eval(itp);
      }
    }

    // Preconditions.

    /*
    pop();
    push(itp);
    push(bmgr.and(left, right));

    boolean res = !isUnsat();
    Model answer = null;

    if (res) {
      answer = getModel();
    }

    if (res == !isUnsat()) {
      return answer.eval(itp);
    }
     */

    return interpolant;
  }

  /*
  private Model solve(BooleanFormula left, BooleanFormula right)
      throws SolverException, InterruptedException, InvalidConfigurationException {

    Model answer = null;

    // set up a basic environment
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    // choose solver
    Solvers solver = Solvers.Z3;

    // setup context
    try (SolverContext context = SolverContextFactory.createSolverContext(config, logger,
        notifier, solver);
         InterpolatingProverEnvironment<?> stack =
             context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS)) {
      logger.log(Level.WARNING, "Using solver " + solver + " in version " + context.getVersion());

      stack.push();

      stack.addConstraint(left);
      stack.addConstraint(right);

      if (!isUnsat()) {
        answer = getModel();
        return answer;
      }

      stack.pop();
    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

      // on some machines we support only some solvers,
      // thus we can ignore these errors.
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");
    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }

    return answer;
  }
   */
}