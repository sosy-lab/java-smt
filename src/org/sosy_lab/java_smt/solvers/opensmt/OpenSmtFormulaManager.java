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
import java.util.Map;
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
  public PTRef parseImpl(String pS) throws IllegalArgumentException {
    return osmtLogic.parseFormula(stripSMTLIB2String(pS));
  }

  @Override
  public String dumpFormulaImpl(PTRef f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    StringBuilder out = new StringBuilder();
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
    out.append("(assert ").append(osmtLogic.dumpWithLets(f)).append(')');
    return out.toString();
  }

  // TODO: this is ignoring escape chars etc.
  private String stripSMTLIB2String(String pFormulaStr) {
    String s = pFormulaStr;
    int commentIndex = s.indexOf(";;");
    while (commentIndex != -1) {
      int endCommentIndex = s.indexOf('\n', commentIndex + 1);
      String s1 = s.substring(0, commentIndex);
      String s2 = s.substring(endCommentIndex + 1);
      s = s1 + s2;
      commentIndex = s.indexOf(";;");
    }
    int setLogicIndex = s.indexOf("(set-logic ");
    if (setLogicIndex != -1) {
      int endLogicIndex = s.indexOf(')', setLogicIndex + 1);
      String s1 = s.substring(0, setLogicIndex);
      String s2 = s.substring(endLogicIndex + 1);
      s = s1 + s2;
    }
    return s;
  }
}
