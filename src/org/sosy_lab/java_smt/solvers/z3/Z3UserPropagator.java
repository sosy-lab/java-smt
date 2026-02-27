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
import com.microsoft.z3.Status;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.UserPropagator;

final class Z3UserPropagator extends UserPropagatorBase implements PropagatorBackend {
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;
  private final UserPropagator userPropagator;
  private final long z3True;
  private final long z3False;

  /* We use this map to reuse existing formula wrappers and avoid creating unnecessary phantom
  references (if enabled). This is particularly useful, because the user propagator frequently
  reports the same formulas. */
  private final Map<Long, Formula> canonicalizer = new HashMap<>();

  Z3UserPropagator(
      long ctx,
      long solver,
      Z3FormulaCreator creator,
      Z3FormulaManager manager,
      UserPropagator userPropagator) {
    super(ctx, solver);
    this.creator = creator;
    this.userPropagator = userPropagator;
    this.manager = manager;
    z3True = creator.extractInfo(manager.getBooleanFormulaManager().makeTrue());
    z3False = creator.extractInfo(manager.getBooleanFormulaManager().makeFalse());
  }

  // ===========================================================================
  // Function calls from Z3's side (forwarding callbacks to the user propagator)
  // ===========================================================================

  @Override
  protected void pushWrapper() {
    userPropagator.onPush();
  }

  @Override
  protected void popWrapper(int num) {
    userPropagator.onPop(num);
  }

  @Override
  protected void finWrapper() {
    userPropagator.onFinalCheck();
  }

  // TODO: This method is not supported for now.
  @Override
  protected void eqWrapper(long pL, long pL1) {}

  @Override
  protected void fixedWrapper(long lvar, long lvalue) {
    assert lvalue == z3True || lvalue == z3False;
    userPropagator.onKnownValue(encapsulateBoolean(lvar), lvalue == z3True);
  }

  // TODO: This method is called if Z3 re-instantiates a user propagator for a sub-problem
  //  (usually when quantifiers are involved). For now, we assume the user propagators to only get
  //  used on quantifier-less formulas so that this method is unnecessary.
  @Override
  protected Z3UserPropagator freshWrapper(long lctx) {
    return this;
  }

  // TODO: This method is called if the user registers a function (currently not
  //  possible) and the solver instantiates the registered function: if the solver
  //  instantiates "forall x: f(x)" at x=y, then f(y) will get created.
  @Override
  protected void createdWrapper(long le) {}

  @Override
  protected void decideWrapper(long lvar, int bit, boolean isPositive) {
    // We currently only allow tracking of decision on boolean formulas,
    // so we ignore the <bit> parameter
    userPropagator.onDecision(encapsulateBoolean(lvar), isPositive);
  }

  @Override
  protected boolean onBindingWrapper(long quantifiedVar, long instantiation) {
    return userPropagator.onBinding(encapsulate(quantifiedVar), encapsulate(instantiation));
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
    Native.propagateConsequence(
        this,
        ctx,
        solver,
        javainfo,
        assignedLiterals.length,
        extractInfoFromArray(assignedLiterals),
        emptyEqs.length,
        emptyEqs,
        emptyEqs,
        creator.extractInfo(consequence));
  }

  @Override
  public boolean propagateNextDecision(BooleanFormula expr, Optional<Boolean> value) {
    Status status =
        value
            .map(pBoolean -> (pBoolean ? Status.SATISFIABLE : Status.UNSATISFIABLE))
            .orElse(Status.UNKNOWN);
    int index = 0; // Only relevant for bitvector expressions, which are not supported yet.
    return Native.propagateNextSplit(
        this, ctx, solver, javainfo, creator.extractInfo(expr), index, status.toInt());
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

  private BooleanFormula encapsulateBoolean(final long z3Expr) {
    return (BooleanFormula) encapsulate(z3Expr);
  }

  private Formula encapsulate(final long z3Expr) {
    // Due to pointer alignment, the lowest 2-3 bits are always 0 which can lead to
    // more collisions in the hashmap. To counteract, we fill the lowest bits by rotating the
    // value. The rotation guarantees a bijective transformation.
    return canonicalizer.computeIfAbsent(
        Long.rotateRight(z3Expr, 3), key -> creator.encapsulateWithTypeOf(z3Expr));
  }

  @Override
  public void close() {
    canonicalizer.clear();
    super.close();
  }
}
