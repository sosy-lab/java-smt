// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC5InterpolatingProver extends CVC5AbstractProver<Term>
    implements InterpolatingProverEnvironment<Term> {

  BooleanFormulaManager bmgr;

  protected CVC5InterpolatingProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      Solver pSolver,
      AtomicBoolean pIsAnyStackAlive) {
    super(
        pFormulaCreator,
        pShutdownNotifier,
        pRandomSeed,
        pOptions,
        pBmgr,
        pSolver,
        pIsAnyStackAlive);
    bmgr = pBmgr;
  }

  @Override
  public Term addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    setChanged();
    Term exp = creator.extractInfo(f);
    assertedFormulas.peek().add(exp);
    if (incremental) {
      solver.assertFormula(exp);
    }
    return exp;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Term> pFormulasOfA)
      throws SolverException, InterruptedException {
    Term interpolTerm;
    if (pFormulasOfA.isEmpty()) {
      interpolTerm = solver.mkBoolean(true);
    } else {
      Term[] terms = pFormulasOfA.toArray(new Term[0]);
      interpolTerm = terms[0];
      for (int i = 1; i < pFormulasOfA.size(); i++) {
        interpolTerm = interpolTerm.andTerm(terms[i]);
      }
    }
    return creator.encapsulateBoolean(solver.getInterpolant(interpolTerm));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Term>> partitionedFormulas)
      throws SolverException, InterruptedException {
    Preconditions.checkArgument(
        !partitionedFormulas.isEmpty(), "at least one partition should be available.");

    // the fallback to a loop is sound and returns an inductive sequence of interpolants
    final List<BooleanFormula> itps = new ArrayList<>();
    for (int i = 1; i < partitionedFormulas.size(); i++) {
      itps.add(
          getInterpolant(
              ImmutableList.copyOf(Iterables.concat(partitionedFormulas.subList(0, i)))));
    }
    return itps;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Term>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "Tree interpolants are not supported. Use another solver.");
  }
}
