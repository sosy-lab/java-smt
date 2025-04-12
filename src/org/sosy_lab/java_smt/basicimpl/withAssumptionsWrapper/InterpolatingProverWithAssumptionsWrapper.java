// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;

public class InterpolatingProverWithAssumptionsWrapper<T>
    extends BasicProverWithAssumptionsWrapper<T, InterpolatingProverEnvironment<T>>
    implements InterpolatingProverEnvironment<T> {

  private final List<T> solverAssumptionsFromPush;
  private final FormulaManager fmgr;
  private final BooleanFormulaManager bmgr;

  public InterpolatingProverWithAssumptionsWrapper(
      InterpolatingProverEnvironment<T> pDelegate, FormulaManager pFmgr) {
    super(pDelegate);
    solverAssumptionsFromPush = new ArrayList<>();
    fmgr = checkNotNull(pFmgr);
    bmgr = fmgr.getBooleanFormulaManager();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    List<T> completeListOfA = new ArrayList<>(pFormulasOfA);
    completeListOfA.addAll(solverAssumptionsFromPush);
    BooleanFormula interpolant = delegate.getInterpolant(completeListOfA);

    // remove assumption variables from the rawInterpolant if necessary
    if (!solverAssumptionsAsFormula.isEmpty()) {
      interpolant =
          bmgr.transformRecursively(interpolant, new RemoveAssumptionsFromFormulaVisitor());
    }

    return interpolant;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    if (solverAssumptionsAsFormula.isEmpty()) {
      return delegate.getSeqInterpolants(pPartitionedFormulas);
    } else {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    if (solverAssumptionsAsFormula.isEmpty()) {
      return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
    } else {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  protected void registerPushedFormula(T pPushResult) {
    solverAssumptionsFromPush.add(pPushResult);
  }

  @Override
  protected void clearAssumptions() {
    super.clearAssumptions();
    solverAssumptionsFromPush.clear();
  }

  final class RemoveAssumptionsFromFormulaVisitor extends BooleanFormulaTransformationVisitor {

    private RemoveAssumptionsFromFormulaVisitor() {
      super(fmgr);
    }

    @Override
    public BooleanFormula visitAtom(BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
      if (decl.getKind() == FunctionDeclarationKind.VAR) {
        String varName = decl.getName();
        // TODO is it sound to replace a variable with TRUE?
        if (solverAssumptionsContainsVar(varName)) {
          return bmgr.makeBoolean(true);
        } else {
          return bmgr.makeVariable(varName);
        }
      } else {
        return atom;
      }
    }

    private boolean solverAssumptionsContainsVar(String variableName) {
      for (BooleanFormula solverVar : solverAssumptionsAsFormula) {
        if (fmgr.extractVariables(solverVar).containsKey(variableName)) {
          return true;
        }
      }
      return false;
    }
  }
}
