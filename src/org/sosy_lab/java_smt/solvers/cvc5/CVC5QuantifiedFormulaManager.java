// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.vectorExpr;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4FormulaCreator;

public class CVC5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  protected CVC5QuantifiedFormulaManager(FormulaCreator<Term, Sort, Solver, Term> pFormulaCreator) {
    super(pFormulaCreator);

    solver = pFormulaCreator.getEnv();
  }

  /*
   * (non-Javadoc) CVC4s quantifier support is dependent on the options used.
   * Without any options it tends to run infenitly on many theories or examples.
   * There are 2 options improving this: full-saturate-quant and sygus-inst.
   * full-saturate-quant is activated in JavaSMT per default.
   * You can try combinations of them, or just one if a query is not solveable.
   * More info on full-saturate-quant: Enables "enumerative instantiation",
   * see: https://homepage.divms.uiowa.edu/~ajreynol/tacas18.pdf
   * More info on sygus-inst: Enables syntax-guided instantiation,
   * see https://homepage.divms.uiowa.edu/~ajreynol/tacas21.pdf
   * This approach tends to work well when the quantified formula involves
   * theories (e.g. strings) where more traditional quantifier instantiation
   * heuristics do not apply.
   * This applies to CVC4 and CVC5!
   */
  @Override
  protected Term eliminateQuantifiers(Expr pExtractInfo)
      throws SolverException, InterruptedException {
    Expr eliminated = pExtractInfo;
    // The first bool is for partial or full elimination. true is full
    // The second bool (optional; 2 methods) is whether to output warnings or not, such as when an
    // unexpected logic is used.
    try {
      eliminated = smtEngine.doQuantifierElimination(pExtractInfo, true);
    } catch (RuntimeException e) {
      // quantifier elimination failed, simply return the input
    }
    // We don't delete it in the prover.close(), is there a reason for that?
    smtEngine.delete();
    return eliminated;
  }

  /*
   * Makes the quantifier entered in CVC4. Note that CVC4 uses bound variables in quantified
   * formulas instead of the normal free vars. We create a bound copy for every var and substitute
   * the free var for the bound var in the body Formula. Note that CVC4 uses their internal Lists
   * for the variable list in quantifiers.
   */
  @Override
  public Term mkQuantifier(Quantifier pQ, List<Expr> pVars, Expr pBody) {
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for quantifier.");
    } else {
      // CVC4 uses its own lists for quantifier that may only have bound vars
      vectorExpr vec = new vectorExpr();
      Expr substBody = pBody;
      // every free needs a bound copy. As the internal Id is different for every variable, even
      // with the same name, this is fine.
      for (Expr var : pVars) {
        Expr boundCopy = ((CVC4FormulaCreator) formulaCreator).makeBoundCopy(var);
        vec.add(boundCopy);
        substBody = substBody.substitute(var, boundCopy);
      }
      Expr quantifiedVars = exprManager.mkExpr(Kind.BOUND_VAR_LIST, vec);

      Kind quant = pQ == Quantifier.EXISTS ? Kind.EXISTS : Kind.FORALL;
      return exprManager.mkExpr(quant, quantifiedVars, substBody);
    }
  }
}
