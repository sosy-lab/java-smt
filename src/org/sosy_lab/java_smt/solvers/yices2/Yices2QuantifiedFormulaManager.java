// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.primitives.Ints;
import com.sri.yices.Terms;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class Yices2QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Integer, Integer, Long, Integer> {

  Yices2QuantifiedFormulaManager(FormulaCreator<Integer, Integer, Long, Integer> pCreator) {
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
        Terms.toString(pBody));

    Yices2FormulaCreator creator = (Yices2FormulaCreator) formulaCreator;
    int[] vars = pVars.stream().mapToInt(creator::createBoundVariableFromFreeVariable).toArray();
    int substBody = Terms.subst(pBody, Ints.toArray(pVars), vars);
    if (pQ == Quantifier.FORALL) {
      return Terms.forall(vars, substBody);
    } else {
      return Terms.exists(vars, substBody);
    }
  }
}
