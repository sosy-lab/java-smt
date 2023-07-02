// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.io.IOException;
import java.util.Map;
import java.util.stream.Collectors;
import opensmt.Logic;
import opensmt.OpenSmt;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import opensmt.Symbol;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class OpenSmtFormulaManager extends AbstractFormulaManager<PTRef, SRef, OpenSmt, SymRef> {
  private final OpenSmtFormulaCreator creator;
  private final Logic osmtLogic;

  OpenSmtFormulaManager(
      OpenSmtFormulaCreator pFormulaCreator,
      OpenSmtUFManager pFfmgr,
      OpenSmtBooleanFormulaManager pBfmgr,
      OpenSmtIntegerFormulaManager pIfmgr,
      OpenSmtRationalFormulaManager pRfmgr,
      OpenSmtArrayFormulaManager pAfmgr) {
    super(pFormulaCreator, pFfmgr, pBfmgr, pIfmgr, pRfmgr, null, null, null, pAfmgr, null, null);

    creator = pFormulaCreator;
    osmtLogic = pFormulaCreator.getEnv().getLogic();
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

          int numArgs = sym.size() - 1;

          if (numArgs == 0) {
            out.append(
                "(declare-const "
                    + osmtLogic.getSymName(ref)
                    + osmtLogic.printSort(sym.rsort())
                    + ")\n");
          } else {
            out.append(
                "(declare-fun "
                    + osmtLogic.getSymName(ref)
                    + " ("
                    + sym.getArgs().stream()
                        .map((atype) -> osmtLogic.printSort(atype))
                        .collect(Collectors.joining(" "))
                    + ") "
                    + osmtLogic.printSort(sym.rsort())
                    + ")\n");
          }
        }
        out.append("(assert " + osmtLogic.pp(f) + ')');
      }
    };
  }
}
