// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;
import java.io.IOException;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.Symbol;

class OpenSmtFormulaManager extends AbstractFormulaManager<PTRef, SRef, Logic, SymRef> {
  private final OpenSmtFormulaCreator creator;
  private final Logic osmtLogic;

  OpenSmtFormulaManager(
      OpenSmtFormulaCreator pFormulaCreator,
      OpenSmtUFManager pFfmgr,
      OpenSmtBooleanFormulaManager pBfmgr,
      OpenSmtIntegerFormulaManager pIfmgr,
      OpenSmtRationalFormulaManager pRfmgr,
      OpenSmtArrayFormulaManager pAfmgr) {
    super(
        pFormulaCreator,
        pFfmgr,
        pBfmgr,
        pIfmgr,
        pRfmgr,
        null,
        null,
        null,
        pAfmgr,
        null,
        null,
        null);

    creator = pFormulaCreator;
    osmtLogic = pFormulaCreator.getEnv();
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    return creator.encapsulateBoolean(osmtLogic.parseFormula(pS));
  }

  @Override
  public Appender dumpFormula(PTRef f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        Map<String, PTRef> userDeclarations = creator.extractVariablesAndUFs(f, true);

        for (PTRef term : userDeclarations.values()) {
          SymRef ref = osmtLogic.getSymRef(term);
          Symbol sym = osmtLogic.getSym(ref);

          out.append("(declare-fun ")
              .append(osmtLogic.protectName(ref))
              .append(" (")
              .append(Joiner.on(' ').join(Lists.transform(sym.getArgTypes(), osmtLogic::printSort)))
              .append(") ")
              .append(osmtLogic.printSort(sym.rsort()))
              .append(")\n");
        }
        out.append("(assert ").append(osmtLogic.dumpWithLets(f)).append(String.valueOf(')'));
      }
    };
  }
}
