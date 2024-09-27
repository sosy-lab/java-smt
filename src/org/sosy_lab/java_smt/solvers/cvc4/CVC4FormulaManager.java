// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Joiner;
import com.google.common.collect.Iterables;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Type;
import java.io.IOException;
import java.io.OutputStream;
import java.util.LinkedHashMap;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC4FormulaManager extends AbstractFormulaManager<Expr, Type, ExprManager, Expr> {

  private final CVC4FormulaCreator creator;

  @SuppressWarnings("checkstyle:parameternumber")
  CVC4FormulaManager(
      CVC4FormulaCreator pFormulaCreator,
      CVC4UFManager pFfmgr,
      CVC4BooleanFormulaManager pBfmgr,
      CVC4IntegerFormulaManager pIfmgr,
      CVC4RationalFormulaManager pRfmgr,
      CVC4BitvectorFormulaManager pBvfmgr,
      CVC4FloatingPointFormulaManager pFpfmgr,
      CVC4QuantifiedFormulaManager pQfmgr,
      CVC4ArrayFormulaManager pAfmgr,
      CVC4SLFormulaManager pSLfmgr,
      CVC4StringFormulaManager pStrmgr) {
    super(
        pFormulaCreator,
        pFfmgr,
        pBfmgr,
        pIfmgr,
        pRfmgr,
        pBvfmgr,
        pFpfmgr,
        pQfmgr,
        pAfmgr,
        pSLfmgr,
        pStrmgr,
        null);
    creator = pFormulaCreator;
  }

  static Expr getCVC4Expr(Formula pT) {
    if (pT instanceof CVC4Formula) {
      return ((CVC4Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  public Expr parseImpl(String formulaStr) throws IllegalArgumentException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Appender dumpFormulaImpl(Expr f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {

        // get all symbols
        final Map<String, Expr> allVars = new LinkedHashMap<>();
        creator.extractVariablesAndUFs(f, true, allVars::put);

        // print all symbols
        for (Map.Entry<String, Expr> entry : allVars.entrySet()) {
          String name = entry.getKey();
          Expr var = entry.getValue();

          // escaping is stolen from SMTInterpol, lets hope this remains consistent
          out.append("(declare-fun ").append(PrintTerm.quoteIdentifier(name)).append(" (");

          // add function parameters
          Iterable<Type> childrenTypes = Iterables.transform(var, Expr::getType);
          out.append(Joiner.on(" ").join(childrenTypes));

          // and return type
          out.append(") ").append(var.getType().toString()).append(")\n");
        }

        // now add the final assert
        out.append("(assert ");
        // f.toString() does expand all nested sub-expressions and causes exponential overhead.
        // f.toStream() uses LET-expressions and is exactly what we want.
        try (OutputStream stream =
            new OutputStream() {

              @Override
              public void write(int chr) throws IOException {
                out.append((char) chr);
              }
            }) {
          f.toStream(stream);
        }
        out.append(')');
      }
    };
  }
}
