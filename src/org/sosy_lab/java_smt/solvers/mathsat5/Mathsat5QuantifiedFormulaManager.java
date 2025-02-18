/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_apply_substitution;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_existentially_quantify;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_not;

import com.google.common.primitives.Longs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;
import org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock;

public class Mathsat5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {
  IUltimateServiceProvider provider =
      org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock
          .createUltimateServiceProviderMock();
  UltimateEliminator ue;
  ILogger iLogger = provider.getLoggingService().getControllerLogger();
  Script interpol = new SMTInterpol();

  private final Long solver;

  private Optional<Mathsat5FormulaManager> fmgr;

  private final LogManager logger;

  protected Mathsat5QuantifiedFormulaManager(
      FormulaCreator<Long, Long, Long, Long> pFormulaCreator, LogManager pLogger) {
    super(pFormulaCreator);

    solver = pFormulaCreator.getEnv();
    fmgr = Optional.empty();
    logger = pLogger;

    ue = new UltimateEliminator(provider, iLogger, interpol);
    ue.setLogic(Logics.AUFNIRA);
  }

  @Override
  protected Long eliminateQuantifiers(Long input) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Long eliminateQuantifiersUltimateEliminator(Long pExtractInfo)
      throws UnsupportedOperationException {
    IUltimateServiceProvider provider =
        UltimateServiceProviderMock.createUltimateServiceProviderMock();
    UltimateEliminator ue;
    ILogger iLogger = provider.getLoggingService().getControllerLogger();
    Script interpol = new SMTInterpol();
    ue = new UltimateEliminator(provider, iLogger, interpol);
    ue.setLogic(Logics.AUFNIRA);

    Mathsat5FormulaManager formulaManager = fmgr.get();
    Term formula =
        UltimateEliminatorParser.parseImpl(
            formulaManager.dumpFormulaImpl(pExtractInfo), logger, ue);
    formula = ue.simplify(formula);
    Long result =
        formulaManager.parseImpl(UltimateEliminatorParser.dumpFormula(formula).toString());
    return result;
  }

  @Override
  public Long mkQuantifier(Quantifier pQ, List<Long> pVars, Long pBody) {
    checkArgument(!pVars.isEmpty(), "List of quantified variables can not be empty");

    long quantifiedFormula;

    List<Long> boundVars = new ArrayList<Long>();
    Long substBody = pBody;

    for (Long var : pVars) {
      Long boundCopy = ((Mathsat5FormulaCreator) formulaCreator).makeBoundCopy(solver, var);
      boundVars.add(boundCopy);

      substBody =
          msat_apply_substitution(solver, substBody, 1, new long[] {var}, new long[] {boundCopy});
    }
    // TODO create terms with bound variables
    if (pQ == Quantifier.EXISTS) {
      quantifiedFormula = msat_existentially_quantify(solver, substBody, Longs.toArray(boundVars));
    } else {
      long negatedFormula = msat_make_not(solver, substBody);
      long existentiallyQuantified =
          msat_existentially_quantify(solver, negatedFormula, Longs.toArray(boundVars));
      quantifiedFormula = msat_make_not(solver, existentiallyQuantified);
    }
    return quantifiedFormula;
  }

  public void setFormulaManager(Mathsat5FormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }
}
