// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;

public class CVC5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  private Optional<CVC5FormulaManager> fmgr;

  private final LogManager logger;

  protected CVC5QuantifiedFormulaManager(
      FormulaCreator<Term, Sort, Solver, Term> pFormulaCreator, LogManager pLogger) {
    super(pFormulaCreator);

    solver = pFormulaCreator.getEnv();
    fmgr = Optional.empty();
    logger = pLogger;
  }

  /*
   * (non-Javadoc) CVC4s quantifier support is dependent on the options used.
   * Without any options it tends to run infinitely on many theories or examples.
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
  protected Term eliminateQuantifiers(Term input) throws SolverException, InterruptedException {
    try {
      return solver.getQuantifierElimination(input);
    } catch (RuntimeException e) {
      // quantifier elimination failed, simply return the input
      return input;
    }
  }

  @Override
  protected Term eliminateQuantifiersUltimateEliminator(Term pExtractInfo)
      throws UnsupportedOperationException {
    IUltimateServiceProvider provider =
        org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock
            .createUltimateServiceProviderMock();
    UltimateEliminator ue;
    ILogger iLogger = provider.getLoggingService().getControllerLogger();
    Script interpol = new SMTInterpol();
    ue = new UltimateEliminator(provider, iLogger, interpol);
    ue.setLogic(Logics.AUFNIRA);

    CVC5FormulaManager formulaManager = fmgr.get();
    de.uni_freiburg.informatik.ultimate.logic.Term formula =
        UltimateEliminatorParser.parseImpl(
            formulaManager.dumpFormulaImpl(pExtractInfo), logger, ue);
    formula = ue.simplify(formula);
    Term result =
        formulaManager.parseImpl(UltimateEliminatorParser.dumpFormula(formula).toString());
    return result;
  }

  /*
   * Makes the quantifier entered in CVC4/CVC5. Note that CVC4/CVC5 uses bound variables in
   * quantified formulas instead of the normal free vars. We create a bound copy for every var
   * and substitute the free var for the bound var in the body Formula. Note that CVC4/CVC5 uses
   * their internal Lists for the variable list in quantifiers.
   */
  @Override
  public Term mkQuantifier(Quantifier pQ, List<Term> pVars, Term pBody) {
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for quantifier.");
    } else {
      List<Term> boundVars = new ArrayList<>();
      Term substBody = pBody;
      // every free needs a bound copy. As the internal Id is different for every variable, even
      // with the same name, this is fine.
      for (Term var : pVars) {
        Term boundCopy = ((CVC5FormulaCreator) formulaCreator).makeBoundCopy(var);
        boundVars.add(boundCopy);
        substBody = substBody.substitute(var, boundCopy);
      }

      Kind quant = pQ == Quantifier.EXISTS ? Kind.EXISTS : Kind.FORALL;
      Term boundVarsList = solver.mkTerm(Kind.VARIABLE_LIST, boundVars.toArray(new Term[0]));
      return solver.mkTerm(quant, boundVarsList, substBody);
    }
  }

  public void setFormulaManager(CVC5FormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }
}
