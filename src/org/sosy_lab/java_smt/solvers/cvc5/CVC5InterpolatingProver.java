// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import io.github.cvc5.Kind;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC5InterpolatingProver extends CVC5AbstractProver<Term>
    implements InterpolatingProverEnvironment<Term> {

  // protected final Deque<List<Term>> assertedFormulas = new ArrayDeque<>();
  private final FormulaManager mgr;
  private final CVC5FormulaCreator creator;
  private final Set<Term> assertedFormulaHash = new HashSet<>();

  CVC5InterpolatingProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      @SuppressWarnings("unused") int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr
      ) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pMgr);
    mgr = pMgr;
    creator = pFormulaCreator;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    for (Term removed : assertedFormulas.peek()) {
      assertedFormulaHash.remove(removed);
    }
    super.pop();
  }

  @Override
  public Term addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    Term t = creator.extractInfo(pConstraint);
    assertedFormulaHash.add(t);

    super.addConstraint(pConstraint);
    return t;
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    R result = super.allSat(pCallback, pImportant);
    return result;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Term> pFormulasOfA)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);

    Set<Term> formulasOfA = ImmutableSet.copyOf(pFormulasOfA);
    // formulasOfB := assertedFormulas - formulas
    Set<Term> formulasOfB =
        assertedFormulaHash.stream()
            .filter(n -> !formulasOfA.contains(n))
            .collect(ImmutableSet.toImmutableSet());


    //Term assertions = solver.mkBoolean(false);

    //for (Term t : pFormulasOfA) {
    //  assertions = solver.mkTerm(Kind.OR, solver.mkTerm(Kind.NEG, t), assertions);
    //}

    // Term itp = solver.getInterpolant(assertions);

    // BooleanFormula result = creator.encapsulateBoolean(itp);

    // return result;
    return Iterables.getOnlyElement(getSeqInterpolants(ImmutableList.of(formulasOfA, formulasOfB)));
  }

  /*
   * @Override public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<Term>>
   * partitionedFormulas) throws SolverException { Preconditions.checkArgument(
   * !partitionedFormulas.isEmpty(), "at least one partition should be available.");
   * 
   * final List<BooleanFormula> itps = new ArrayList<>(); for (int i = 1; i <
   * partitionedFormulas.size(); i++) { itps.add( getInterpolant(
   * ImmutableList.copyOf(Iterables.concat(partitionedFormulas.subList(0, i))))); } return itps; }
   */

  @Override
  public List<BooleanFormula>
      getTreeInterpolants(List<? extends Collection<Term>> pPartitionedFormulas, int[] pStartOfSubTree)
          throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    assert InterpolatingProverEnvironment
        .checkTreeStructure(pPartitionedFormulas.size(), pStartOfSubTree);

    // final Term[] formulas =
    // pPartitionedFormulas.stream().map(x -> buildConjunctionOfFormulas(x)).toArray(Term[]::new);

    ArrayList<ArrayList<ArrayList<Collection<Term>>>> interpolationPairs =
        getTreeInterpolationPairs(pPartitionedFormulas, pStartOfSubTree);

    // final Term[] itps;
    final ArrayList<Term> itps = new ArrayList<>();
    try {
      for (int i = 0; i < interpolationPairs.size(); i++) {
        // Term interpolant = getCVC5Interpolation(interpolationPairs.get(i));
        itps.add(getCVC5Interpolation(interpolationPairs.get(i)));
      }
      // itps = (Term[]) interpolationPairs.stream().map(n -> getCVC5Interpolation(n)).toArray();
    } catch (UnsupportedOperationException e) {
      if (e.getMessage() != null) {// Test when occures
        throw new SolverException(e.getMessage(), e);
      } else {
        throw e;
      }
    }

    final List<BooleanFormula> result = new ArrayList<>();
    for (Term itp : itps) {
      result.add(creator.encapsulateBoolean(itp));
    }
    assert result.size() == pStartOfSubTree.length - 1;
    return result;
  }

  private Term getCVC5Interpolation(ArrayList<ArrayList<Collection<Term>>> formulaPair) {
    assert formulaPair.size() == 2;

    Deque<List<Term>> assertedFormulasCopy = assertedFormulas; // Clone/Copy not Working???
    Set<Term> assertedFormulaHashCopy = assertedFormulaHash;

    ArrayList<Collection<Term>> assertedInterpols = formulaPair.get(0);
    ArrayList<Collection<Term>> addedInterpols = formulaPair.get(1);

    ArrayList<Collection<Term>> combinedInterpols = new ArrayList<Collection<Term>>();
    combinedInterpols.addAll(assertedInterpols);
    combinedInterpols.addAll(addedInterpols);

    Collection<Term> extraAssertions =
        getAssertedTermsNotInCollection(combinedInterpols);
    Term extraAssert = new Term();

    if (extraAssertions.size() == 0) {
      extraAssert = solver.mkTrue();
    } else {
      extraAssert = buildConjunctionOfFormulas(extraAssertions);
    }

    Term phim = buildConjunctionOfCollectionOfFormula(assertedInterpols);
    Term phip = buildConjunctionOfCollectionOfFormula(addedInterpols);

    solver.resetAssertions();
    solver.assertFormula(solver.mkTerm(Kind.AND, extraAssert, phim));

    Term interpolant = solver.getInterpolant(solver.mkTerm(Kind.NOT, phip));

    solver.resetAssertions();

    assertedFormulaHash.forEach((n) -> solver.assertFormula(n));

    return interpolant;

  }

  private Collection<Term> getAssertedTermsNotInCollection(ArrayList<Collection<Term>> collTerms) {
    Set<Term> assertedTerms = ImmutableSet.copyOf(assertedFormulaHash);
    ArrayList<Term> retTerms = new ArrayList<Term>();
    collTerms.forEach((n) -> retTerms.addAll(n));
    Set<Term> filteredAssertedTerms =
        assertedFormulaHash.stream()
            .filter(n -> !retTerms.contains(n))
            .collect(ImmutableSet.toImmutableSet());
    return filteredAssertedTerms;
  }

  private Term buildConjunctionOfCollectionOfFormula(ArrayList<Collection<Term>> formula) {
    ArrayList<Collection<Term>> recformula = new ArrayList<Collection<Term>>();
    Collection<Term> currColTerm = formula.get(0);
    formula.remove(0);
    if (formula.size() == 0) {
      return buildConjunctionOfFormulas(currColTerm);
    }
    return solver.mkTerm(
        Kind.AND,
        buildConjunctionOfFormulas(currColTerm),
        buildConjunctionOfCollectionOfFormula(formula));
  }

  // Generates Pairs of Interpolants
  private ArrayList<ArrayList<ArrayList<Collection<Term>>>> getTreeInterpolationPairs(
      List<? extends Collection<Term>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    ArrayList<ArrayList<ArrayList<Collection<Term>>>> result = new ArrayList<>(); // Exp
                                                                                  // [[[A,B],[C]],[[A],[B,C]]]
    ArrayList<Collection<Term>> currA = new ArrayList<Collection<Term>>();// Exp [(A),(B)]
    ArrayList<Collection<Term>> currB = new ArrayList<Collection<Term>>(pPartitionedFormulas);
    ArrayList<ArrayList<Collection<Term>>> betweenRes =
        new ArrayList<ArrayList<Collection<Term>>>();
    ArrayList<Collection<Term>> copyOfFormulas =
        new ArrayList<Collection<Term>>(pPartitionedFormulas);
    List<Integer> leafes = new ArrayList<Integer>();

    leafes.add(pStartOfSubTree[0]);

    currA.add(copyOfFormulas.get(0));
    currB.remove(0);
    betweenRes.add((ArrayList<Collection<Term>>) currA.clone());
    betweenRes.add((ArrayList<Collection<Term>>) currB.clone());
    result.add(betweenRes);
    betweenRes = new ArrayList<ArrayList<Collection<Term>>>();
    for (int i = 1; i < pStartOfSubTree.length - 1; i++) {
      if (pStartOfSubTree[i] == pStartOfSubTree[i - 1]) {
        currA.add(copyOfFormulas.get(i));
        currB.remove(0);
        betweenRes.add((ArrayList<Collection<Term>>) currA.clone());
        betweenRes.add((ArrayList<Collection<Term>>) currB.clone());
      } else {
        if (leafes.contains(pStartOfSubTree[i])) {
          currA = new ArrayList<Collection<Term>>();
          currB = new ArrayList<Collection<Term>>();
          for (int j = 0; j < pStartOfSubTree.length; i++) {
            if (j <= i) {
              currA.add(copyOfFormulas.get(j));
            } else {
              currB.add(copyOfFormulas.get(j));
            }
          }
          betweenRes.add((ArrayList<Collection<Term>>) currA.clone());
          betweenRes.add((ArrayList<Collection<Term>>) currB.clone());
        } else {
          currB.addAll(currA);
          currA = new ArrayList<Collection<Term>>();
          currA.add(copyOfFormulas.get(i));
          currB.remove(0);
          betweenRes.add((ArrayList<Collection<Term>>) currA.clone());
          betweenRes.add((ArrayList<Collection<Term>>) currB.clone());
          leafes.add(pStartOfSubTree[i]);
        }
      }
      result.add(betweenRes);
      betweenRes = new ArrayList<ArrayList<Collection<Term>>>();
    }
    assert result.size() == pStartOfSubTree.length - 1;
    return result;
  }

  private List<Collection<Term>> invertSelection(
      List<? extends Collection<Term>> pPartitionedFormulas,
      List<Collection<Term>> currSelection) {
    return pPartitionedFormulas.stream()
        .filter(n -> !currSelection.contains(n))
        .collect(ImmutableList.toImmutableList());
  }

  private Term buildConjunctionOfFormulas(Collection<Term> formulas) {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(!formulas.isEmpty());

    Term formula = formulas.iterator().next();

    // formulas.remove(formula); // doens't work?

    Collection<Term> removedFormulas =
        formulas.stream().filter(n -> !formula.equals(n)).collect(ImmutableList.toImmutableList());

    if (removedFormulas.size() == 0) {
      return formula;
    }

    return solver.mkTerm(Kind.AND, formula, buildConjunctionOfFormulas(removedFormulas));
  }

}
