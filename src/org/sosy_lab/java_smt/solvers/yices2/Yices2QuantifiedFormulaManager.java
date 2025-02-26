// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exists;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_forall;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_subst_term;

import com.google.common.primitives.Ints;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;

public class Yices2QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Integer, Integer, Long, Integer> {

  private Optional<Yices2FormulaManager> fmgr;
  private final LogManager logger;

  protected Yices2QuantifiedFormulaManager(
      FormulaCreator<Integer, Integer, Long, Integer> pCreator, LogManager pLogger) {
    super(pCreator);
    fmgr = Optional.empty();
    logger = pLogger;
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
      List<Integer> yicesVars = new ArrayList<>();
      for (int var : pVars) {
        yicesVars.add(((Yices2FormulaCreator) formulaCreator).makeVariable(var));
      }
      int substBody = pBody;
      substBody =
          yices_subst_term(
              yicesVars.size(), Ints.toArray(pVars), Ints.toArray(yicesVars), substBody);

      int[] terms = Ints.toArray(yicesVars);
      if (pQ == Quantifier.FORALL) {
        return yices_forall(terms.length, terms, substBody);
      } else if (pQ == Quantifier.EXISTS) {
        return yices_exists(terms.length, terms, substBody);
      }
    }
    return null;
  }

  @Override
  protected Integer eliminateQuantifiersUltimateEliminator(Integer pExtractInfo)
      throws UnsupportedOperationException, IOException {
    IUltimateServiceProvider provider =
        org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock
            .createUltimateServiceProviderMock();
    UltimateEliminator ue;
    ILogger iLogger = provider.getLoggingService().getControllerLogger();
    Script interpol = new SMTInterpol();
    ue = new UltimateEliminator(provider, iLogger, interpol);
    ue.setLogic(Logics.AUFNIRA);

    Yices2FormulaManager formulaManager = fmgr.get();
    Term formula =
        UltimateEliminatorParser.parseImpl(
            formulaManager.dumpFormulaImpl(pExtractInfo), logger, ue);
    formula = ue.simplify(formula);
    Integer result =
        formulaManager.parseImpl(UltimateEliminatorParser.dumpFormula(formula).toString());
    return result;
  }

  public void setFormulaManager(Yices2FormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }

  public LogManager getLogger() {
    return logger;
  }
}
