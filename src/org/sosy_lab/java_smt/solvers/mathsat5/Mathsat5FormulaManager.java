// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_apply_substitution;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_from_smtlib2;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_copy_from;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_simplify;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_to_smtlib2;

import com.google.common.collect.Collections2;
import com.google.common.primitives.Longs;
import java.util.Collection;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class Mathsat5FormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  @SuppressWarnings("checkstyle:parameternumber")
  Mathsat5FormulaManager(
      Mathsat5FormulaCreator creator,
      Mathsat5UFManager pFunctionManager,
      Mathsat5BooleanFormulaManager pBooleanManager,
      Mathsat5IntegerFormulaManager pIntegerManager,
      Mathsat5RationalFormulaManager pRationalManager,
      Mathsat5BitvectorFormulaManager pBitpreciseManager,
      Mathsat5FloatingPointFormulaManager pFloatingPointManager,
      Mathsat5ArrayFormulaManager pArrayManager,
      Mathsat5EnumerationFormulaManager pEnumerationManager) {
    super(
        creator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        null,
        pArrayManager,
        null,
        null,
        pEnumerationManager);
  }

  static long getMsatTerm(Formula pT) {
    return ((Mathsat5Formula) pT).getTerm();
  }

  static long[] getMsatTerm(Collection<? extends Formula> pFormulas) {
    return Longs.toArray(Collections2.transform(pFormulas, Mathsat5FormulaManager::getMsatTerm));
  }

  @Override
  public Long parseImpl(String pS) throws IllegalArgumentException {
    return msat_from_smtlib2(getEnvironment(), pS);
  }

  @Override
  public String dumpFormulaImpl(final Long f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    // FIXME Mathsat tries to escape the |...| quotes in the symbol. This is not allowed by the
    //  SMTLIB standard and should be report as a bug.
    String r = msat_to_smtlib2(getEnvironment(), f);
    return r.replaceAll("\\\\\\|", "");
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    long[] changeFrom = new long[fromToMapping.size()];
    long[] changeTo = new long[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator()
        .encapsulate(
            type,
            msat_apply_substitution(
                getFormulaCreator().getEnv(),
                extractInfo(f),
                fromToMapping.size(),
                changeFrom,
                changeTo));
  }

  @Override
  protected Long simplify(Long f) throws InterruptedException {
    // we need to keep all variables, otherwise we will not return a equisatisfiable formula.
    // TODO we could expand the interface and let the user choose the variables.
    final Map<String, Long> variables = getFormulaCreator().extractVariablesAndUFs(f, true);
    final long[] protectedSymbols = Longs.toArray(variables.values());
    return msat_simplify(getFormulaCreator().getEnv(), f, protectedSymbols);
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (otherManager instanceof Mathsat5FormulaManager) {
      long otherMsatContext = ((Mathsat5FormulaManager) otherManager).getEnvironment();
      if (otherMsatContext == getEnvironment()) {

        // Same context.
        return formula;
      } else {

        // Msat5 to Msat5 translation.
        long translatedFormula =
            msat_make_copy_from(getEnvironment(), extractInfo(formula), otherMsatContext);
        return getFormulaCreator().encapsulateBoolean(translatedFormula);
      }
    }
    return super.translateFrom(formula, otherManager);
  }
}
