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

import static org.sosy_lab.solver.z3java.Z3BitvectorFormulaManager.toBV;
import static org.sosy_lab.solver.z3java.Z3BooleanFormulaManager.toBool;
import static org.sosy_lab.solver.z3java.Z3NumeralFormulaManager.toAE;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;

import java.io.IOException;
import java.util.List;
import java.util.Map;

final class Z3FormulaManager extends AbstractFormulaManager<Expr, Sort, Context, FuncDecl> {

  @SuppressWarnings("checkstyle:parameternumber")
  Z3FormulaManager(
      Z3FormulaCreator pFormulaCreator,
      Z3UFManager pFunctionManager,
      Z3BooleanFormulaManager pBooleanManager,
      Z3IntegerFormulaManager pIntegerManager,
      Z3RationalFormulaManager pRationalManager,
      Z3BitvectorFormulaManager pBitpreciseManager,
      Z3FloatingPointFormulaManager pFloatingPointManager,
      Z3QuantifiedFormulaManager pQuantifiedManager,
      Z3ArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        pQuantifiedManager,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String str) throws IllegalArgumentException {

    // TODO do we need sorts or decls?
    // the context should know them already,
    // TODO check this
    Symbol[] sortSymbols = new Symbol[0];
    Sort[] sorts = new Sort[0];
    Symbol[] declSymbols = new Symbol[0];
    FuncDecl[] decls = new FuncDecl[0];
    BoolExpr e = getEnvironment().parseSMTLIB2String(str, sortSymbols, sorts, declSymbols, decls);

    return getFormulaCreator().encapsulateBoolean(e);
  }

  private static final ImmutableMap<Tactic, String> Z3_TACTICS =
      ImmutableMap.<Tactic, String>builder()
          .put(Tactic.NNF, "nnf")
          .put(Tactic.CNF, "cnf")
          .put(Tactic.TSEITIN_CNF, "tseitin-cnf")
          .put(Tactic.QE, "qe")
          .put(Tactic.QE_LIGHT, "qe-light")
          .build();

  @Override
  protected Expr applyTacticImpl(Expr input, Tactic tactic) throws InterruptedException {
    String z3TacticName = Z3_TACTICS.get(tactic);
    if (z3TacticName != null) {
      return Z3NativeApiHelpers.applyTactic(
          getFormulaCreator().getEnv(), toBool(input), z3TacticName);
    } else {
      return super.applyTacticImpl(input, tactic);
    }
  }

  @Override
  public Appender dumpFormula(final Expr expr) {
    assert getFormulaCreator().getFormulaType(expr) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {

        // Serializing a solver is a simplest way to dump a formula in Z3,
        // cf https://github.com/Z3Prover/z3/issues/397
        Solver z3solver = getEnvironment().mkSolver();
        z3solver.add((BoolExpr) expr);
        String serialized = z3solver.toString();
        out.append(serialized);
      }
    };
  }

  @Override
  protected Expr simplify(Expr pF) {
    return pF.simplify();
  }

  @Override
  protected List<? extends Expr> splitNumeralEqualityIfPossible(Expr pF) {
    Context z3context = getFormulaCreator().getEnv();
    if (pF.isEq() && pF.getNumArgs() == 2) {
      Expr arg0 = pF.getArgs()[0];
      Expr arg1 = pF.getArgs()[1];

      Z3_sort_kind sortKind = arg0.getSort().getSortKind();
      assert sortKind == arg1.getSort().getSortKind();
      if (sortKind == Z3_sort_kind.Z3_BV_SORT) {

        Expr out1 = z3context.mkBVULE(toBV(arg0), toBV(arg1));
        Expr out2 = z3context.mkBVUGE(toBV(arg0), toBV(arg1));

        return ImmutableList.of(out1, out2);
      } else if (sortKind == Z3_sort_kind.Z3_INT_SORT || sortKind == Z3_sort_kind.Z3_REAL_SORT) {

        Expr out1 = z3context.mkLe(toAE(arg0), toAE(arg1));
        Expr out2 = z3context.mkGe(toAE(arg0), toAE(arg1));
        return ImmutableList.of(out1, out2);
      }
    }
    return ImmutableList.of(pF);
  }

  @Override
  public <T extends Formula> T substitute(
      T pF, Map<? extends Formula, ? extends Formula> pFromToMapping) {
    return substituteUsingLists(pF, pFromToMapping);
  }

  @Override
  protected Expr substituteUsingListsImpl(Expr t, List<Expr> changeFrom, List<Expr> changeTo) {
    int size = changeFrom.size();
    Preconditions.checkState(size == changeTo.size());
    return t.substitute(changeFrom.toArray(new Expr[changeFrom.size()]),
        changeTo.toArray(new Expr[changeTo.size()]));
  }

  @Override
  public BooleanFormula translate(BooleanFormula other, SolverContext otherContext) {
    FormulaManager otherManager = otherContext.getFormulaManager();
    if (otherManager instanceof Z3FormulaManager) {
      Z3FormulaManager o = (Z3FormulaManager) otherManager;
      Context otherZ3Context = o.getEnvironment();
      if (otherZ3Context == getEnvironment()) {

        // Same context.
        return other;
      } else {

        // Z3-to-Z3 translation.
        Expr translatedAST = extractInfo(other).translate(getEnvironment());
        return getFormulaCreator().encapsulateBoolean(translatedAST);
      }
    }
    return super.translate(other, otherContext);
  }
}
