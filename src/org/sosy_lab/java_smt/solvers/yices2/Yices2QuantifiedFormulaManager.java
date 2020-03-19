/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  SPDX-License-Identifier: Apache-2.0 AND GPL-3.0-or-later
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exists;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_forall;

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
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("Yices does not support eliminating Quantifiers.");
  }

  @Override
  public Integer mkQuantifier(Quantifier pQ, List<Integer> pVars, Integer pBody) {
    /*
     * TODO Yices needs variables constructed using yices_new_variable(), but variables passed in
     * pVars are constructed with yices_new uninterpreted_term(). Need to construct the correct
     * variable type from the variables in pVars and map between them.
     */
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for Quantifier.");
    } else {
      int[] terms = Ints.toArray(pVars);
      if (pQ == Quantifier.FORALL) {
        return yices_forall(terms.length, terms, pBody);
      } else if (pQ == Quantifier.EXISTS) {
        return yices_exists(terms.length, terms, pBody);
      }
    }
    return null;
  }
}
