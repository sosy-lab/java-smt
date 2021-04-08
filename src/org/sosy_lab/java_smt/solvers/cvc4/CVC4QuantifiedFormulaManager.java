// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class CVC4QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  protected CVC4QuantifiedFormulaManager(
      FormulaCreator<Expr, Type, ExprManager, Expr> pFormulaCreator) {
    super(pFormulaCreator);
    exprManager = pFormulaCreator.getEnv();
  }

  @Override
  protected Expr eliminateQuantifiers(Expr pExtractInfo)
      throws SolverException, InterruptedException {
    // TODO Implements this! The exception is temporary as CVC4 supports this for LIA and LRA
    throw new UnsupportedOperationException("Yices does not support eliminating Quantifiers.");
  }

  /*
   * pBody needs to be a bound var (mkBoundVar()). This is currently not working because of bound
   * variables! TODO: Use visitor to subsitute all bound variables by unbound
   *
   */
  @Override
  public Expr mkQuantifier(Quantifier pQ, List<Expr> pVars, Expr pBody) {
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for Quantifier.");
    } else {
      // CVC4 has its own "lists"
      // I dont know if this is the way to go, its how the CVC4 devs did it in their examples.
      // TODO: recheck
      vectorExpr vec = new vectorExpr();
      pVars.stream().forEach(vec::add);
      Expr quantifiedVars = exprManager.mkExpr(Kind.BOUND_VAR_LIST, vec);
      if (pQ == Quantifier.FORALL) {
        return exprManager.mkExpr(Kind.FORALL, quantifiedVars, pBody);
      } else if (pQ == Quantifier.EXISTS) {
        return exprManager.mkExpr(Kind.EXISTS, quantifiedVars, pBody);
      }
    }
    return null;
  }

}
