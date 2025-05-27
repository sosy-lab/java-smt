/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.UnmodifiableIterator;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;

@SuppressWarnings({"unchecked", "UnusedVariable"})
public class PortfolioBooleanFormulaManager implements BooleanFormulaManager {

  private final PortfolioFormulaCreator creator;

  protected PortfolioBooleanFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public BooleanFormula makeTrue() {
    // The solvers cache this, we could as well
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> solverAndMgr :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      BooleanFormulaManager solverMgr = solverAndMgr.getValue();
      finalFormulaBuilder.put(solver, solverMgr.makeTrue());
    }

    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula makeFalse() {
    // The solvers cache this, we could as well
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> solverAndMgr :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      BooleanFormulaManager solverMgr = solverAndMgr.getValue();
      finalFormulaBuilder.put(solver, solverMgr.makeFalse());
    }

    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> solverAndMgr :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      BooleanFormulaManager solverMgr = solverAndMgr.getValue();
      finalFormulaBuilder.put(solver, solverMgr.makeVariable(pVar));
    }

    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2) {
    assert formula1 instanceof PortfolioBooleanFormula;
    assert formula2 instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();
      BooleanFormula specF2 =
          ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().get(solver);
      finalFormulaBuilder.put(solver, checkNotNull(mgr).equivalence(specF1, checkNotNull(specF2)));
    }

    checkState(
        ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().size()
            == ((PortfolioBooleanFormula) formula2).getFormulasPerSolver().size());
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2) {
    assert formula1 instanceof PortfolioBooleanFormula;
    assert formula2 instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();
      BooleanFormula specF2 =
          ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().get(solver);
      finalFormulaBuilder.put(solver, checkNotNull(mgr).implication(specF1, checkNotNull(specF2)));
    }

    checkState(
        ((PortfolioBooleanFormula) formula1).getFormulasPerSolver().size()
            == ((PortfolioBooleanFormula) formula2).getFormulasPerSolver().size());
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public boolean isTrue(BooleanFormula formula) {
    assert formula instanceof PortfolioBooleanFormula;
    PortfolioBooleanFormula portfolioFormula = ((PortfolioBooleanFormula) formula);
    for (Entry<Solvers, BooleanFormulaManager> solverAndMgr :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      BooleanFormulaManager solverMgr = solverAndMgr.getValue();
      BooleanFormula specificFormula = portfolioFormula.getFormulasPerSolver().get(solver);

      boolean res = solverMgr.isTrue(checkNotNull(specificFormula));
      assert creator.getSolverSpecificBooleanFormulaManagers().entrySet().stream()
          .allMatch(
              e ->
                  e.getValue().isTrue(portfolioFormula.getFormulasPerSolver().get(e.getKey()))
                      == res);
      return res;
    }
    throw new IllegalStateException("Portfolio solving without solver not allowed.");
  }

  @Override
  public boolean isFalse(BooleanFormula formula) {
    assert formula instanceof PortfolioBooleanFormula;
    for (Entry<Solvers, BooleanFormulaManager> solverAndMgr :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      BooleanFormulaManager solverMgr = solverAndMgr.getValue();
      BooleanFormula specificFormula =
          ((PortfolioBooleanFormula) formula).getFormulasPerSolver().get(solver);

      boolean res = solverMgr.isFalse(checkNotNull(specificFormula));
      assert creator.getSolverSpecificBooleanFormulaManagers().entrySet().stream()
          .allMatch(
              e ->
                  e.getValue()
                          .isFalse(
                              ((PortfolioBooleanFormula) formula)
                                  .getFormulasPerSolver()
                                  .get(e.getKey()))
                      == res);
      return res;
    }
    throw new IllegalStateException("Portfolio solving without solver not allowed.");
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2) {
    assert cond instanceof PortfolioBooleanFormula;
    assert f1 instanceof PortfolioFormula;
    assert f2 instanceof PortfolioFormula;

    ImmutableMap.Builder<Solvers, T> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> solversAndManager :
        creator.getSolverSpecificBooleanFormulaManagers().entrySet()) {
      Solvers solver = solversAndManager.getKey();
      BooleanFormulaManager mgr = solversAndManager.getValue();
      BooleanFormula specificCond =
          ((PortfolioBooleanFormula) cond).getFormulasPerSolver().get(solver);
      T specificF1 = (T) ((PortfolioFormula) f1).getFormulasPerSolver().get(solver);
      T specificF2 = (T) ((PortfolioFormula) f2).getFormulasPerSolver().get(solver);
      if (mgr != null && specificF1 != null && specificCond != null && specificF2 != null) {
        finalFormulaBuilder.put(solver, mgr.ifThenElse(specificCond, specificF1, specificF2));
      }
    }
    ImmutableMap<Solvers, T> finalFormula = finalFormulaBuilder.buildOrThrow();
    return creator.encapsulate(creator.getFormulaType(finalFormula), finalFormula);
  }

  @Override
  public BooleanFormula not(BooleanFormula bits) {
    assert bits instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> entry1 :
        ((PortfolioBooleanFormula) bits).getFormulasPerSolver().entrySet()) {
      Solvers solver = entry1.getKey();
      BooleanFormulaManager solverMgr =
          creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      checkNotNull(solverMgr); // We generally don't expect bool to be missing
      finalFormulaBuilder.put(solver, solverMgr.not(entry1.getValue()));
    }

    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2) {
    assert bits1 instanceof PortfolioBooleanFormula;
    assert bits2 instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();
      BooleanFormula specF2 = ((PortfolioBooleanFormula) bits2).getFormulasPerSolver().get(solver);
      finalFormulaBuilder.put(solver, checkNotNull(mgr).and(specF1, checkNotNull(specF2)));
    }

    checkState(
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().size()
            == ((PortfolioBooleanFormula) bits2).getFormulasPerSolver().size());
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> bits) {
    switch (bits.size()) {
      case 0:
        return makeTrue();
      case 1:
        return bits.iterator().next();
      case 2:
        Iterator<BooleanFormula> it = bits.iterator();
        return and(it.next(), it.next());
      default:
        return andImpl(bits);
    }
  }

  @Override
  public BooleanFormula and(BooleanFormula... bits) {
    return and(Arrays.asList(bits));
  }

  /**
   * Create an n-ary conjunction. The default implementation delegates to {@link
   * #and(BooleanFormula, BooleanFormula)} and assumes that all simplifications are done by that
   * method. This method can be overridden, in which case it should filter out irrelevant operands.
   *
   * @param pParams A collection of at least 3 operands.
   * @return A term that is equivalent to a conjunction of pParams.
   */
  protected BooleanFormula andImpl(Collection<BooleanFormula> pParams) {
    BooleanFormula result = makeTrue();
    for (BooleanFormula formula : ImmutableSet.copyOf(pParams)) {
      if (isFalse(formula)) {
        return formula;
      }
      result = and(result, formula);
    }
    return result;
  }

  protected BooleanFormula orImpl(Collection<BooleanFormula> pParams) {
    BooleanFormula result = makeFalse();
    for (BooleanFormula formula : ImmutableSet.copyOf(pParams)) {
      if (isTrue(formula)) {
        return formula;
      }
      result = or(result, formula);
    }
    return result;
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  public BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2) {
    assert bits1 instanceof PortfolioBooleanFormula;
    assert bits2 instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();
      BooleanFormula specF2 = ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().get(solver);
      finalFormulaBuilder.put(solver, checkNotNull(mgr).or(specF1, checkNotNull(specF2)));
    }

    checkState(
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().size()
            == ((PortfolioBooleanFormula) bits2).getFormulasPerSolver().size());
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> bits) {
    switch (bits.size()) {
      case 0:
        return makeFalse();
      case 1:
        return bits.iterator().next();
      case 2:
        Iterator<BooleanFormula> it = bits.iterator();
        return or(it.next(), it.next());
      default:
        return orImpl(bits);
    }
  }

  @Override
  public BooleanFormula or(BooleanFormula... bits) {
    return or(Arrays.asList(bits));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  public BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2) {
    assert bits1 instanceof PortfolioBooleanFormula;
    assert bits2 instanceof PortfolioBooleanFormula;

    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();
      BooleanFormula specF2 = ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().get(solver);
      finalFormulaBuilder.put(solver, checkNotNull(mgr).xor(specF1, checkNotNull(specF2)));
    }

    checkState(
        ((PortfolioBooleanFormula) bits1).getFormulasPerSolver().size()
            == ((PortfolioBooleanFormula) bits2).getFormulasPerSolver().size());
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    assert pFormula instanceof PortfolioBooleanFormula;
    // TODO: LOG this with warning, as this works only for transformations etc.
    System.out.println(
        "Warning: portfolio solver visitation is applying all visitations to all "
            + "nested solvers");
    // ImmutableMap.Builder<Solvers, R> finalFormulaBuilder = ImmutableMap.builder();
    R res = null;
    FormulaType<?> type = null;
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) pFormula).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();

      // TODO: sensible?
      R resSpecific = mgr.visit(specF1, visitor);
      if (res == null) {
        res = resSpecific;
      }
      checkState(resSpecific == res);
      // finalFormulaBuilder.put(solver, res);
    }
    // This is most likely not a good idea^^
    return checkNotNull(res);
  }

  @Override
  public void visitRecursively(
      BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor) {
    assert f instanceof PortfolioBooleanFormula;

    // TODO: LOG this with warning, as this works only for transformations etc.
    System.out.println(
        "Warning: portfolio solver visitation is applying all visitations to all "
            + "nested solvers");
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();

      mgr.visitRecursively(specF1, rFormulaVisitor);
    }
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    assert f instanceof PortfolioBooleanFormula;
    // TODO: LOG this with warning, as this works only for transformations etc.
    System.out.println(
        "Warning: portfolio solver visitation is applying all visitations to all "
            + "nested solvers");
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();

      finalFormulaBuilder.put(solver, mgr.transformRecursively(specF1, pVisitor));
    }
    return creator.encapsulateBoolean(finalFormulaBuilder.buildOrThrow());
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    assert f instanceof PortfolioBooleanFormula;
    // TODO: LOG this with warning, as this works only for transformations etc.
    System.out.println(
        "Warning: portfolio solver visitation is applying all visitations to all nested solvers."
            + " The order of formulas returned might be wrong for toConjunctionArgs()");
    ImmutableSet.Builder<BooleanFormula> finalFormulasSetBuilder = ImmutableSet.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();

      ImmutableSet<BooleanFormula> alreadyTransformed = finalFormulasSetBuilder.build();
      UnmodifiableIterator<BooleanFormula> alreadyTransformedIterator =
          alreadyTransformed.iterator();
      finalFormulasSetBuilder = ImmutableSet.builder();
      for (BooleanFormula specificFormula : mgr.toConjunctionArgs(specF1, flatten)) {
        ImmutableMap.Builder<Solvers, BooleanFormula> specificCollector = ImmutableMap.builder();
        specificCollector.put(solver, specificFormula);
        // Add all already known
        if (alreadyTransformedIterator.hasNext()) {
          BooleanFormula elementFromOtherSolver = alreadyTransformedIterator.next();
          for (Entry<Solvers, BooleanFormula> others :
              ((PortfolioBooleanFormula) elementFromOtherSolver)
                  .getFormulasPerSolver()
                  .entrySet()) {
            specificCollector.put(others.getKey(), others.getValue());
          }
        }
        finalFormulasSetBuilder.add(creator.encapsulateBoolean(specificCollector.buildOrThrow()));
      }
    }

    return finalFormulasSetBuilder.build();
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    assert f instanceof PortfolioBooleanFormula;
    // TODO: LOG this with warning, as this works only for transformations etc.
    System.out.println(
        "Warning: portfolio solver visitation is applying all visitations to all nested solvers."
            + " The order of formulas returned might be wrong for toDisjunctionArgs()");
    ImmutableSet.Builder<BooleanFormula> finalFormulasSetBuilder = ImmutableSet.builder();
    for (Entry<Solvers, BooleanFormula> f1Formulas :
        ((PortfolioBooleanFormula) f).getFormulasPerSolver().entrySet()) {
      Solvers solver = f1Formulas.getKey();
      BooleanFormulaManager mgr = creator.getSolverSpecificBooleanFormulaManagers().get(solver);
      BooleanFormula specF1 = f1Formulas.getValue();

      ImmutableSet<BooleanFormula> alreadyTransformed = finalFormulasSetBuilder.build();
      UnmodifiableIterator<BooleanFormula> alreadyTransformedIterator =
          alreadyTransformed.iterator();
      finalFormulasSetBuilder = ImmutableSet.builder();
      for (BooleanFormula specificFormula : mgr.toDisjunctionArgs(specF1, flatten)) {
        ImmutableMap.Builder<Solvers, BooleanFormula> specificCollector = ImmutableMap.builder();
        specificCollector.put(solver, specificFormula);
        // Add all already known
        if (alreadyTransformedIterator.hasNext()) {
          BooleanFormula elementFromOtherSolver = alreadyTransformedIterator.next();
          for (Entry<Solvers, BooleanFormula> others :
              ((PortfolioBooleanFormula) elementFromOtherSolver)
                  .getFormulasPerSolver()
                  .entrySet()) {
            specificCollector.put(others.getKey(), others.getValue());
          }
        }
        finalFormulasSetBuilder.add(creator.encapsulateBoolean(specificCollector.buildOrThrow()));
      }
    }

    return finalFormulasSetBuilder.build();
  }
}
