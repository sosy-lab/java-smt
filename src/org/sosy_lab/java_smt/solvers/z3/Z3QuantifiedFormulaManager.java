// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;

class Z3QuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final Z3FormulaCreator z3FormulaCreator;

  private Optional<Z3FormulaManager> fmgr;
  private final LogManager logger;

  Z3QuantifiedFormulaManager(Z3FormulaCreator creator, LogManager pLogger) {
    super(creator);
    this.z3context = creator.getEnv();
    z3FormulaCreator = creator;
    fmgr = Optional.empty();
    logger = pLogger;
  }

  @Override
  public Long mkQuantifier(Quantifier q, List<Long> pVariables, Long pBody) {
    checkArgument(!pVariables.isEmpty(), "List of quantified variables can not be empty");
    return Native.mkQuantifierConst(
        z3context,
        q == Quantifier.FORALL,
        0,
        pVariables.size(),
        Longs.toArray(pVariables),
        0,
        new long[0],
        pBody);
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    // It is recommended (personal communication with Nikolaj Bjorner)
    // to run "qe-light" before "qe".
    // "qe" does not perform a "qe-light" as a preprocessing on its own!

    // One might want to run the tactic "ctx-solver-simplify" on the result.

    return z3FormulaCreator.applyTactics(z3context, pExtractInfo, "qe-light", "qe");
  }

  @Override
  protected Long eliminateQuantifiersUltimateEliminator(Long pExtractInfo)
      throws UnsupportedOperationException {
    IUltimateServiceProvider provider =
        org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock
            .createUltimateServiceProviderMock();
    UltimateEliminator ue;
    ILogger iLogger = provider.getLoggingService().getControllerLogger();
    Script interpol = new SMTInterpol();
    ue = new UltimateEliminator(provider, iLogger, interpol);
    ue.setLogic(Logics.AUFNIRA);

    Z3FormulaManager formulaManager = fmgr.get();
    Term formula =
        UltimateEliminatorParser.parseImpl(
            formulaManager.dumpFormulaImpl(pExtractInfo), logger, ue);
    formula = ue.simplify(formula);
    Long result =
        formulaManager.parseImpl(UltimateEliminatorParser.dumpFormula(formula).toString());
    return result;
  }

  public void setFormulaManager(Z3FormulaManager pFmgr) {
    fmgr = Optional.of(pFmgr);
  }

  public LogManager getLogger() {
    return logger;
  }
}
