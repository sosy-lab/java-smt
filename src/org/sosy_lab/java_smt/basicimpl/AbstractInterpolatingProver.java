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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.ArrayFormulaImpl;

public abstract class AbstractInterpolatingProver<TFormulaInfo, TType>
        extends AbstractProverWithAllSat<TFormulaInfo>
        implements InterpolatingProverEnvironment<TFormulaInfo> {

  private final FormulaCreator<TFormulaInfo, TType, ?, ?> creator;
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
    creator = (FormulaCreator<TFormulaInfo, TType, ?, ?>) pCreator;
    qfmgr = pQfmgr;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
          throws SolverException, InterruptedException {
    return getModelBasedInterpolant(pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
          List<? extends Collection<TFormulaInfo>> partitionedFormulas,
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
  private BooleanFormula getModelBasedInterpolant(Collection<TFormulaInfo> pFormulasOfA) {
    checkState(!closed);
    checkArgument(getAssertedConstraintIds().containsAll(pFormulasOfA),
            "interpolation can only be done over previously asserted formulas.");

    // free arithmetic variables a and b
    final Set<?> assertedFormulas = transformedImmutableSetCopy(getAssertedFormulas(),
            creator::extractInfo);
    final Set<?> a = ImmutableSet.copyOf(pFormulasOfA);
    final Set<?> b = Sets.difference(assertedFormulas, a);

    // shared variables between a and b
    final Set<Formula> sharedFormulas = (Set<Formula>) Sets.intersection(a, b);

    Builder<TType> typesForSharedBuilder = ImmutableList.builder();
    for (Formula var : sharedFormulas) {
      if (var instanceof IntegerFormula) {
        ArrayFormulaImpl varInt = (ArrayFormulaImpl) var;
        FormulaType indexType = varInt.getIndexType();
        FormulaType elementType = varInt.getElementType();
        typesForSharedBuilder.add(creator.getArrayType((TType) indexType, (TType) elementType));
      }
    }
    List<TType> typesForShared = typesForSharedBuilder.build();

    return null;
  }
}
