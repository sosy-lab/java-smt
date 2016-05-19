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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3FormulaCreator.isOP;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

final class Z3FormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

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
    long[] sortSymbols = new long[0];
    long[] sorts = new long[0];
    long[] declSymbols = new long[0];
    long[] decls = new long[0];
    long e = Native.parseSmtlib2String(
        getEnvironment(),
        str,
        sorts.length,
        sortSymbols,
        sorts,
        declSymbols.length,
        declSymbols,
        decls);

    return getFormulaCreator().encapsulateBoolean(e);
  }

  static long getZ3Expr(Formula pT) {
    if (pT instanceof Z3Formula) {
      return ((Z3Formula) pT).getFormulaInfo();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  protected BooleanFormula applyQELightImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "qe-light");
  }

  @Override
  protected BooleanFormula applyCNFImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "tseitin-cnf");
  }

  @Override
  protected BooleanFormula applyNNFImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "nnf");
  }

  private BooleanFormula applyTacticImpl(BooleanFormula pF, String tacticName)
      throws InterruptedException {
    long out =
        Z3NativeApiHelpers.applyTactic(getFormulaCreator().getEnv(), extractInfo(pF), tacticName);
    return getFormulaCreator().encapsulateBoolean(out);
  }

  @Override
  public Appender dumpFormula(final Long expr) {
    assert getFormulaCreator().getFormulaType(expr) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {

        // Serializing a solver is a simplest way to dump a formula in Z3,
        // cf https://github.com/Z3Prover/z3/issues/397
        long z3solver = Native.mkSolver(getEnvironment());
        Native.solverIncRef(getEnvironment(), z3solver);
        Native.solverAssert(getEnvironment(), z3solver, expr);
        String serialized = Native.solverToString(getEnvironment(), z3solver);
        Native.solverDecRef(getEnvironment(), z3solver);
        out.append(serialized);
      }
    };
  }

  @Override
  protected Long simplify(Long pF) {
    return Native.simplify(getFormulaCreator().getEnv(), pF);
  }

  @Override
  protected List<? extends Long> splitNumeralEqualityIfPossible(Long pF) {
    long z3context = getFormulaCreator().getEnv();
    if (isOP(z3context, pF, Z3_decl_kind.Z3_OP_EQ.toInt())
        && Native.getAppNumArgs(z3context, pF) == 2) {
      long arg0 = Native.getAppArg(z3context, pF, 0);
      Native.incRef(z3context, arg0);
      long arg1 = Native.getAppArg(z3context, pF, 1);
      Native.incRef(z3context, arg1);

      try {
        long sortKind = Native.getSortKind(z3context, Native.getSort(z3context, arg0));
        assert sortKind == Native.getSortKind(z3context, Native.getSort(z3context, arg1));
        if (sortKind == Z3_sort_kind.Z3_BV_SORT.toInt()) {

          long out1 = Native.mkBvule(z3context, arg0, arg1);
          Native.incRef(z3context, out1);
          long out2 = Native.mkBvuge(z3context, arg0, arg1);
          Native.incRef(z3context, out2);

          return ImmutableList.of(out1, out2);
        } else if (sortKind == Z3_sort_kind.Z3_INT_SORT.toInt()
            || sortKind == Z3_sort_kind.Z3_REAL_SORT.toInt()) {

          long out1 = Native.mkLe(z3context, arg0, arg1);
          Native.incRef(z3context, out1);
          long out2 = Native.mkGe(z3context, arg0, arg1);
          Native.incRef(z3context, out2);
          return ImmutableList.of(out1, out2);
        }
      } finally {
        Native.decRef(z3context, arg0);
        Native.decRef(z3context, arg1);
      }
    }
    return ImmutableList.of(pF);
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    long[] changeFrom = new long[fromToMapping.size()];
    long[] changeTo = new long[fromToMapping.size()];
    int idx = 0;
    for (Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator()
        .encapsulate(
            type,
            Native.substitute(
                getFormulaCreator().getEnv(),
                extractInfo(f),
                fromToMapping.size(),
                changeFrom,
                changeTo));
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula other, FormulaManager otherManager) {
    if (otherManager instanceof Z3FormulaManager) {
      Z3FormulaManager o = (Z3FormulaManager) otherManager;
      long otherZ3Context = o.getEnvironment();
      if (otherZ3Context == getEnvironment()) {

        // Same context.
        return other;
      } else {

        // Z3-to-Z3 translation.
        long translatedAST =
            Native.translate(otherZ3Context, extractInfo(other), getEnvironment());
        return getFormulaCreator().encapsulateBoolean(translatedAST);
      }
    }
    return super.translateFrom(other, otherManager);
  }
}
