// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;


import com.microsoft.z3.Native;
import com.microsoft.z3.Native.UserPropagatorBase;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.UserPropagator;

final class Z3UserPropagator extends UserPropagatorBase implements PropagatorBackend {
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;
  private final UserPropagator userPropagator;

  Z3UserPropagator(
      long ctx, long solver, Z3FormulaCreator creator, Z3FormulaManager manager,
      UserPropagator userPropagator) {
    super(ctx, solver);
    this.creator = creator;
    this.userPropagator = userPropagator;
    this.manager = manager;
  }

  // ===========================================================================
  // Function calls from Z3's side (forwarding callbacks to the user propagator)
  // ===========================================================================

  @Override
  public void pushWrapper() {
    userPropagator.onPush();
  }

  @Override
  public void popWrapper(int num) {
    userPropagator.onPop(num);
  }

  @Override
  public void finWrapper() {
    userPropagator.onFinalCheck();
  }

  // TODO: This method is not supported for now.
  @Override
  protected void eqWrapper(long pL, long pL1) {

  }

  @Override
  public void fixedWrapper(long lvar, long lvalue) {
    userPropagator.onKnownValue(encapsulate(lvar), encapsulate(lvalue));
  }

  // TODO: This method is called if Z3 re-instantiates a user propagator for a subproblem
  //  (usually when quantifiers are involved). For now, we assume the user propagators to only get
  //  used on quantifier-less formulas so that this method is unnecessary.
  @Override
  public Z3UserPropagator freshWrapper(long lctx) {
    return this;
  }

  // TODO: This method is called if the user registers a function (currently not
  //  possible) and the solver instantiates the registered function: if the solver
  //  instantiates "forall x: f(x)" at x=y, then f(y) will get created.
  @Override
  public void createdWrapper(long le) {
  }

  @Override
  protected void decideWrapper(long lvar, int bit, boolean is_pos) {
    // We currently only allow tracking of decision on boolean formulas
    // so we ignore the <bit> parameter
    userPropagator.onDecision(encapsulate(lvar), is_pos);
  }


  // ===========================================================================
  // Function calls from JavaSMT's side (mostly calls to the smt backend)
  // ===========================================================================

  @Override
  public void registerExpression(BooleanFormula exprToWatch) {
    Native.propagateAdd(this, ctx, solver, javainfo, creator.extractInfo(exprToWatch));
  }

  @Override
  public void notifyOnKnownValue() {
    registerFixed();
  }

  @Override
  public void notifyOnDecision() {
    registerDecide();
  }

  @Override
  public void notifyOnFinalCheck() {
    registerFinal();
  }

  @Override
  public void propagateConflict(BooleanFormula[] conflictExpressions) {
    propagateConsequence(conflictExpressions, manager.getBooleanFormulaManager().makeFalse());
  }

  @Override
  public void propagateConsequence(BooleanFormula[] assignedLiterals, BooleanFormula consequence) {
    long[] emptyEqs = new long[0];
    Native.propagateConsequence(this, ctx, solver, javainfo,
        assignedLiterals.length,
        extractInfoFromArray(assignedLiterals),
        emptyEqs.length,
        emptyEqs,
        emptyEqs,
        creator.extractInfo(consequence)
    );
  }

  private enum Z3LBool {
    FALSE(-1),
    UNDEFINED(0),
    TRUE(1);

    final int value;

    Z3LBool(int value) {
      this.value = value;
    }
  }

  @Override
  public boolean propagateNextDecision(BooleanFormula expr, Optional<Boolean> value) {
    Z3LBool phase = value.map(pBoolean -> (pBoolean ? Z3LBool.TRUE : Z3LBool.FALSE))
        .orElse(Z3LBool.UNDEFINED);
    int index = 0; // Only relevant for bitvector expressions, which are not supported yet.
    return Native.propagateNextSplit(this, ctx, solver, javainfo, creator.extractInfo(expr),
        index, phase.value);
  }

  private long[] extractInfoFromArray(BooleanFormula[] formulaArray) {
    long[] formulaInfos = new long[formulaArray.length];
    for (int i = 0; i < formulaArray.length; i++) {
      if (formulaArray[i] != null) {
        formulaInfos[i] = creator.extractInfo(formulaArray[i]);
      }
    }
    return formulaInfos;
  }

  private BooleanFormula encapsulate(long z3Expr) {
    return creator.encapsulateBoolean(z3Expr);
  }
}
