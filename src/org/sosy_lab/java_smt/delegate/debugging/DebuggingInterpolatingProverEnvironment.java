// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class DebuggingInterpolatingProverEnvironment<T> extends DebuggingBasicProverEnvironment<T>
    implements InterpolatingProverEnvironment<T> {
  private final FormulaManager delegateFormulaManager;
  private final InterpolatingProverEnvironment<T> delegate;

  public DebuggingInterpolatingProverEnvironment(
      InterpolatingProverEnvironment<T> pDelegate,
      FormulaManager pFormulaManager,
      Set<Formula> pLocalFormulas) {
    super(pDelegate, pLocalFormulas);
    delegateFormulaManager = checkNotNull(pFormulaManager);
    delegate = checkNotNull(pDelegate);
  }

  // FIXME: Some as in DebuggingFormulaManager. Maybe this could be moved elsewhere?
  private class Closure extends DefaultFormulaVisitor<TraversalProcess> {
    @Override
    protected TraversalProcess visitDefault(Formula f) {
      addFormulaToContext(f);
      return TraversalProcess.CONTINUE;
    }
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    // FIXME: We should probably check that the formula ids are valid
    BooleanFormula result = delegate.getInterpolant(formulasOfA);
    delegateFormulaManager.visitRecursively(result, new Closure());
    return result;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    List<BooleanFormula> result = delegate.getSeqInterpolants(partitionedFormulas);
    for (BooleanFormula t : result) {
      delegateFormulaManager.visitRecursively(t, new Closure());
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    assertThreadLocal();
    List<BooleanFormula> result = delegate.getTreeInterpolants(partitionedFormulas, startOfSubTree);
    for (BooleanFormula t : result) {
      delegateFormulaManager.visitRecursively(t, new Closure());
    }
    return result;
  }
}
