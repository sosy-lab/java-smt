// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class SolverLessFormulaManager
    extends AbstractFormulaManager<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFormulaManager(
      SolverLessFormulaCreator pCreator, SolverLessBooleanFormulaManager bmgr) {
    super(
        pCreator,
        new SolverLessUFManager(pCreator),
        bmgr,
        new SolverLessIntegerFormulaManager(pCreator),
        new SolverLessRationalFormulaManager(pCreator),
        new SolverLessBitvectorFormulaManager(pCreator, bmgr),
        new SolverLessFloatingPointFormulaManager(pCreator),
        null,
        new SolverLessArrayFormulaManager(pCreator),
        null,
        new SolverLessStringFormulaManager(pCreator),
        null);
  }

  @Override
  public Appender dumpFormula(final SMTLIB2Formula formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        Generator.assembleConstraint(formula);
        out.append(Generator.getLines());
      }
    };
  }

  @Override
  public SMTLIB2Formula parse(String smtLib) throws IllegalArgumentException {
    return (SMTLIB2Formula) universalParseFromString(smtLib);
  }
}
