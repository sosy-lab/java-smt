/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.ultimate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.solvers.smtinterpol.UltimateEliminatorParser;

public class UltimateEliminatorWrapper {
  private final IUltimateServiceProvider provider;
  private final ILogger iLogger;
  private final UltimateEliminator ultimateEliminator;
  private final Script interpol;
  LogManager log;

  public UltimateEliminatorWrapper(LogManager pLog){
    provider =
        org.sosy_lab.java_smt.test.ultimate.UltimateServiceProviderMock
            .createUltimateServiceProviderMock();
    ;
    iLogger = provider.getLoggingService().getControllerLogger();
    interpol = new SMTInterpol();
    ultimateEliminator = new UltimateEliminator(provider, iLogger, interpol);
    ultimateEliminator.setLogic(Logics.AUFNIRA);
    log = pLog;
  }

  public Term simplify(Term pTerm){
    return ultimateEliminator.simplify(pTerm);
  }

  public Term parse(String pString){
    return UltimateEliminatorParser.parseImpl(pString, log, ultimateEliminator);
  }

  public Appender dumpFormula(Term pFormula){
    return UltimateEliminatorParser.dumpFormula(pFormula);
  }

  public UltimateEliminator getUltimateEliminator(){
    return ultimateEliminator;
  }

}
