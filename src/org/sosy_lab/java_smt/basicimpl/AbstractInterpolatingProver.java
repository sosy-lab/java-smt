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

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolatingProver<F> extends AbstractProverWithAllSat<F>
    implements InterpolatingProverEnvironment<F> {

  private final FormulaCreator<?, ?, ?, ?> creator;
  private final QuantifiedFormulaManager qfmgr;
  private final BooleanFormulaManager bmgr;

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      FormulaCreator<?, ?, ?, ?> pCreator,
      QuantifiedFormulaManager pQfmgr) {
    super(pOptions, pBmgr, pShutdownNotifier);
    bmgr = pBmgr;
    creator = pCreator;
    qfmgr = pQfmgr;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<F> pFormulasOfA)
      throws SolverException, InterruptedException {
    return getModelBasedInterpolant(pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<F>> partitionedFormulas,
      int[] startOfSubTree) throws SolverException, InterruptedException {
    return List.of();
  }

  /**
   * As = free_arith_vars(A)
   * Bs = free_arith_vars(B)
   *
   * shared = [s for s in As & Bs ]
   *
   * Itp = z3.Function('Itp', [s.sort() for s in shared] + [z3.BoolSort()])
   * left = z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
   * right = z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))
   *
   * res, answer = solve_horn([left, right])
   *
   * if res == z3.sat:
   *    return answer.eval(Itp(shared))
   * return None
   */
  private BooleanFormula getModelBasedInterpolant(Collection<F> pFormulasOfA) {
    checkState(!closed);
    checkArgument(getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    // free arithmetic variables a and b
    final Set<?> assertedFormulas = transformedImmutableSetCopy(getAssertedFormulas(),
        creator::extractInfo);
    final Set<?> a = ImmutableSet.copyOf(pFormulasOfA);
    final Set<?> b = Sets.difference(assertedFormulas, a);

    // shared variables between a and b
    final Set<?> sharedFormulas = Sets.intersection(a, b);


    return null;
  }
}
