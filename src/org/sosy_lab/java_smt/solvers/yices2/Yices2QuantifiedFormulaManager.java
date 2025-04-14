// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exists;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_forall;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_subst_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;

import com.google.common.primitives.Ints;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Yices2QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2QuantifiedFormulaManager(
      FormulaCreator<Integer, Integer, Long, Integer> pCreator) {
    super(pCreator);
  }

  @Override
  protected Integer eliminateQuantifiers(Integer pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Yices2 does not support quantifier elimination.");
  }

  @Override
  public Integer mkQuantifier(Quantifier pQ, List<Integer> pVars, Integer pBody) {
    checkArgument(
        !pVars.isEmpty(),
        "Missing variables for quantifier '%s' and body '%s'.",
        pQ,
        yices_term_to_string(pBody));

    Yices2FormulaCreator creator = (Yices2FormulaCreator) formulaCreator;
    int[] vars = pVars.stream().mapToInt(creator::createBoundVariableFromFreeVariable).toArray();
    int substBody = yices_subst_term(vars.length, Ints.toArray(pVars), vars, pBody);
    if (pQ == Quantifier.FORALL) {
      return yices_forall(vars.length, vars, substBody);
    } else {
      return yices_exists(vars.length, vars, substBody);
    }
  }
}
