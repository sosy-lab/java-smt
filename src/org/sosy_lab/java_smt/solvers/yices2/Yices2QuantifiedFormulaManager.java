// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yicesBoundVariableFromUnbound;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exists;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_forall;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_subst_term;

import com.google.common.primitives.Ints;
import java.util.ArrayList;
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
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("Yices does not support eliminating Quantifiers.");
  }

  @Override
  public Integer mkQuantifier(Quantifier pQ, List<Integer> pVars, Integer pBody) {
    // Quantifier support is very limited in Yices2
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for Quantifier.");
    } else {
      List<Integer> yicesVars = new ArrayList<>();
      for (int var : pVars) {
        yicesVars.add(yicesBoundVariableFromUnbound(var));
      }
      int substBody = pBody;
      substBody =
          yices_subst_term(
              yicesVars.size(), Ints.toArray(pVars), Ints.toArray(yicesVars), substBody);

      int[] terms = Ints.toArray(yicesVars);
      if (pQ == Quantifier.FORALL) {
        return yices_forall(terms.length, terms, substBody);
      } else {
        return yices_exists(terms.length, terms, substBody);
      }
    }
  }
}
