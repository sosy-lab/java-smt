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
import org.sosy_lab.java_smt.api.FormulaManager;
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
  private final FormulaManager mgr;
  private final QuantifiedFormulaManager qfmgr;
  private final BooleanFormulaManager bmgr;

  protected AbstractInterpolatingProver(
          Set<ProverOptions> pOptions,
          FormulaManager pMgr,
          BooleanFormulaManager pBmgr,
          QuantifiedFormulaManager pQfmgr,
          ShutdownNotifier pShutdownNotifier,
          FormulaCreator<?, ?, ?, ?> pCreator) {
    super(pOptions, pMgr, pBmgr, pQfmgr, pShutdownNotifier);
    mgr = pMgr;
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

    final Set<TFormulaInfo> assertedFormulas = (Set<TFormulaInfo>) getAssertedFormulas();
    final Set<TFormulaInfo> formulasOfA = ImmutableSet.copyOf(pFormulasOfA);
    final Set<TFormulaInfo> formulasOfB = Sets.difference(assertedFormulas, formulasOfA);

    Set<TFormulaInfo> varOfA = Set.of();
    Set<TFormulaInfo> varOfB = Set.of();

    // free arithmetic variables a and b
    for (TFormulaInfo formula : formulasOfA) {
      TFormulaInfo f = creator.extractInfo((Formula) formula);
      Set<TFormulaInfo> arithVarOfA =
          (Set<TFormulaInfo>) mgr.extractVariablesAndUFs(creator.encapsulateBoolean(f)).keySet();
      varOfA = arithVarOfA;
    }

    for (TFormulaInfo formula : formulasOfB) {
      TFormulaInfo f = creator.extractInfo((Formula) formula);
      Set<TFormulaInfo> arithVarOfB =
          (Set<TFormulaInfo>) mgr.extractVariablesAndUFs(creator.encapsulateBoolean(f)).keySet();
      varOfB = arithVarOfB;
    }

    // shared variables between a and b
    final Set<TFormulaInfo> sharedVars = Sets.intersection(varOfA, varOfB);

    Builder<TType> typesForSharedBuilder = ImmutableList.builder();
    for (TFormulaInfo var : sharedVars) {
      creator.getFormulaType(var);
    }
    List<TType> typesForShared = typesForSharedBuilder.build();

    return null;
  }
}
