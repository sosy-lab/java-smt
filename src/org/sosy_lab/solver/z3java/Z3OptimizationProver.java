/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.z3java;

import static org.sosy_lab.solver.z3java.Z3NumeralFormulaManager.toAE;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Optimize.Handle;
import com.microsoft.z3.Params;
import com.microsoft.z3.RatNum;
import com.microsoft.z3.Status;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;
import org.sosy_lab.solver.api.OptimizationProverEnvironment;
import org.sosy_lab.solver.api.RationalFormulaManager;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import javax.annotation.Nullable;

class Z3OptimizationProver extends Z3AbstractProver<Void> implements OptimizationProverEnvironment {

  private final FormulaManager mgr;
  private final RationalFormulaManager rfmgr;
  private final LogManager logger;
  private static final String Z3_INFINITY_REPRESENTATION = "oo";
  private final Optimize z3optContext;

  // TODO maybe we should replace the List by a Generic interface and
  // use the Handle directly as return-value.
  // This would also reduce the memory-usage here.
  /** We use a List like a HashMap, for the mapping of index to handle. */
  private final List<Handle> handles = new ArrayList<>();

  Z3OptimizationProver(
      FormulaManager mgr,
      Z3FormulaCreator creator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(creator, pShutdownNotifier);
    this.mgr = mgr;
    rfmgr = mgr.getRationalFormulaManager();
    z3optContext = z3context.mkOptimize();
    logger = pLogger;
  }

  private int putToMap(Handle handle) {
    // mapping: position -> handle
    int key = handles.size();
    handles.add(handle);
    return key;
  }

  private Handle getFromMap(int index) {
    // mapping: position -> handle
    return handles.get(index);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    trackConstraint(constraint);
    BoolExpr z3Constraint = (BoolExpr) creator.extractInfo(constraint);
    z3optContext.Add(z3Constraint);
    return null;
  }

  @Override
  public int maximize(Formula objective) {
    Preconditions.checkState(!closed);
    Handle handle = z3optContext.MkMaximize(toAE(creator.extractInfo(objective)));
    return putToMap(handle);
  }

  @Override
  public int minimize(Formula objective) {
    Preconditions.checkState(!closed);
    Handle handle = z3optContext.MkMinimize(toAE(creator.extractInfo(objective)));
    return putToMap(handle);
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Status status = z3optContext.Check();
    if (status == Status.UNSATISFIABLE) {
      return OptStatus.UNSAT;
    } else if (status == Status.UNKNOWN) {
      logger.log(
          Level.INFO,
          "Solver returned an unknown status, explanation: ",
          z3optContext.getReasonUnknown());
      return OptStatus.UNDEF;
    } else {
      return OptStatus.OPT;
    }
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    z3optContext.Push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    z3optContext.Pop();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    return check() == OptStatus.UNSAT;
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    Preconditions.checkState(!closed);
    ArithExpr ast = getFromMap(handle).getUpper();
    if (isInfinity(ast)) {
      return Optional.absent();
    }
    return Optional.of(rationalFromZ3AST(replaceEpsilon(ast, epsilon)));
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    Preconditions.checkState(!closed);
    ArithExpr ast = getFromMap(handle).getLower();
    if (isInfinity(ast)) {
      return Optional.absent();
    }
    return Optional.of(rationalFromZ3AST(replaceEpsilon(ast, epsilon)));
  }

  @Override
  protected Model getZ3Model() {
    return z3optContext.getModel();
  }

  void setParam(String key, String value) {
    Params params = z3context.mkParams();
    params.add(key, value);
    z3optContext.setParameters(params);
  }

  /**
   * Dumps the optimized objectives and the constraints on the solver in the
   * SMT-lib format. Super-useful!
   */
  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return z3optContext.toString();
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    closed = true;
  }

  private boolean isInfinity(ArithExpr pAst) {
    return pAst.toString().contains(Z3_INFINITY_REPRESENTATION);
  }

  /**
   * Replace the epsilon in the returned formula with a numeric value.
   */
  private Expr replaceEpsilon(ArithExpr pAst, Rational newValue) {
    final Formula z;
    if (pAst instanceof IntNum) {
      z = creator.encapsulate(FormulaType.IntegerType, pAst);
    } else if (pAst instanceof RatNum) {
      z = creator.encapsulate(FormulaType.RationalType, pAst);
    } else {
      throw new AssertionError(
          String.format("unexpected type of expression %s (%s)", pAst, pAst.getClass()));
    }

    RationalFormula epsFormula = rfmgr.makeVariable("epsilon");

    Formula out =
        mgr.substitute(
            z,
            ImmutableMap.<Formula, Formula>of(epsFormula, rfmgr.makeNumber(newValue.toString())));
    return creator.extractInfo(out).simplify();
  }

  private Rational rationalFromZ3AST(Expr ast) {
    return Rational.ofString(ast.toString());
  }

  @Override
  public String dump() {
    Preconditions.checkState(!closed);
    return z3optContext.toString();
  }
}
