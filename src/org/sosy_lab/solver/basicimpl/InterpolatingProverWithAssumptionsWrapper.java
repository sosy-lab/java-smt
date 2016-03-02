package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.Lists;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

public class InterpolatingProverWithAssumptionsWrapper<T>
    implements InterpolatingProverEnvironmentWithAssumptions<T> {

  private final List<T> solverAssumptionsFromPush;
  private final List<BooleanFormula> solverAssumptionsAsFormula;
  private final InterpolatingProverEnvironment<T> delegate;
  private final FormulaManager fmgr;
  private final BooleanFormulaManager bmgr;

  public InterpolatingProverWithAssumptionsWrapper(
      InterpolatingProverEnvironment<T> pDelegate, FormulaManager pFmgr) {
    delegate = checkNotNull(pDelegate);
    solverAssumptionsFromPush = new ArrayList<>();
    solverAssumptionsAsFormula = new ArrayList<>();
    fmgr = checkNotNull(pFmgr);
    bmgr = fmgr.getBooleanFormulaManager();
  }

  @Override
  public T push(BooleanFormula pF) {
    clearAssumptions();
    return delegate.push(pF);
  }

  @Override
  public BooleanFormula getInterpolant(List<T> pFormulasOfA)
      throws SolverException, InterruptedException {
    List<T> completeListOfA = Lists.newArrayList(pFormulasOfA);
    completeListOfA.addAll(solverAssumptionsFromPush);
    BooleanFormula interpolant = delegate.getInterpolant(completeListOfA);

    // remove assumption variables from the rawInterpolant if necessary
    if (!solverAssumptionsAsFormula.isEmpty()) {
      interpolant = bmgr.visit(new RemoveAssumptionsFromFormulaVisitor(), interpolant);
    }

    return interpolant;
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    if (solverAssumptionsAsFormula.isEmpty()) {
      return delegate.getSeqInterpolants(pPartitionedFormulas);
    } else {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<T>> pPartitionedFormulas, int[] pStartOfSubTree)
      throws SolverException, InterruptedException {
    if (solverAssumptionsAsFormula.isEmpty()) {
      return delegate.getTreeInterpolants(pPartitionedFormulas, pStartOfSubTree);
    } else {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public void pop() {
    clearAssumptions();
    delegate.pop();
  }

  @Override
  public T addConstraint(BooleanFormula constraint) {
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() {
    clearAssumptions();
    delegate.push();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    clearAssumptions();
    return delegate.isUnsat();
  }

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public boolean isUnsatWithAssumptions(List<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    clearAssumptions();

    solverAssumptionsAsFormula.addAll(assumptions);
    for (BooleanFormula formula : assumptions) {
      solverAssumptionsFromPush.add(delegate.push(formula));
    }
    return delegate.isUnsat();
  }

  private void clearAssumptions() {
    for (int i = 0; i < solverAssumptionsAsFormula.size(); i++) {
      delegate.pop();
    }
    solverAssumptionsAsFormula.clear();
    solverAssumptionsFromPush.clear();
  }

  class RemoveAssumptionsFromFormulaVisitor extends BooleanFormulaTransformationVisitor {

    private RemoveAssumptionsFromFormulaVisitor() {
      super(fmgr, new HashMap<BooleanFormula, BooleanFormula>());
    }

    @Override
    public BooleanFormula visitAtom(BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
      if (decl.getKind() == FunctionDeclarationKind.VAR) {
        String varName = decl.getName();
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
        if (fmgr.extractVariables(solverVar).keySet().contains(variableName)) {
          return true;
        }
      }
      return false;
    }
  }
}
