// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.collect.Iterables.getOnlyElement;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class SmtInterpolFormulaManager
    extends AbstractFormulaManager<Term, Sort, Script, FunctionSymbol> {

  private final LogManager logger;

  SmtInterpolFormulaManager(
      SmtInterpolFormulaCreator pCreator,
      SmtInterpolUFManager pFunctionManager,
      SmtInterpolBooleanFormulaManager pBooleanManager,
      SmtInterpolIntegerFormulaManager pIntegerManager,
      SmtInterpolRationalFormulaManager pRationalManager,
      SmtInterpolArrayFormulaManager pArrayFormulaManager,
      LogManager pLogger) {
    super(
        pCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        null,
        null,
        null,
        pArrayFormulaManager,
        null,
        null,
        null);
    logger = pLogger;
  }

  BooleanFormula encapsulateBooleanFormula(Term t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public Term parseImpl(String pS) throws IllegalArgumentException {
    FormulaCollectionScript parseScript =
        new FormulaCollectionScript(getEnvironment(), getEnvironment().getTheory());
    LogProxy logProxy = new LogProxyForwarder(logger.withComponentName("SMTInterpol"));
    final ParseEnvironment parseEnv =
        new ParseEnvironment(parseScript, new OptionMap(logProxy, true)) {
          @Override
          public void printError(String pMessage) {
            throw new SMTLIBException(pMessage);
          }

          @Override
          public void printSuccess() {}
        };

    try {
      parseEnv.parseStream(new StringReader(pS), "<stdin>");
    } catch (SMTLIBException nested) {
      throw new IllegalArgumentException(nested);
    }

    Term term = getOnlyElement(parseScript.getAssertedTerms());
    return new FormulaUnLet().unlet(term);
  }

  @Override
  public Appender dumpFormulaImpl(final Term formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {
        Set<Term> seen = new HashSet<>();
        Set<FunctionSymbol> declaredFunctions = new HashSet<>();
        Deque<Term> todo = new ArrayDeque<>();
        PrintTerm termPrinter = new PrintTerm();

        todo.addLast(formula);

        while (!todo.isEmpty()) {
          Term t = todo.removeLast();
          while (t instanceof AnnotatedTerm) {
            t = ((AnnotatedTerm) t).getSubterm();
          }
          if (!(t instanceof ApplicationTerm) || !seen.add(t)) {
            continue;
          }

          ApplicationTerm term = (ApplicationTerm) t;
          Collections.addAll(todo, term.getParameters());

          FunctionSymbol func = term.getFunction();
          if (func.isIntern()) {
            continue;
          }

          if (func.getDefinition() == null) {
            if (declaredFunctions.add(func)) {
              out.append("(declare-fun ");
              out.append(PrintTerm.quoteIdentifier(func.getName()));
              out.append(" (");
              int counter = 0;
              for (Sort paramSort : func.getParameterSorts()) {
                termPrinter.append(out, paramSort);

                if (++counter < func.getParameterSorts().length) {
                  out.append(' ');
                }
              }
              out.append(") ");
              termPrinter.append(out, func.getReturnSort());
              out.append(")\n");
            }
          } else {
            // We would have to print a (define-fun) command and
            // recursively traverse into func.getDefinition() (in post-order!).
            // However, such terms should actually not occur.
            throw new IllegalArgumentException("Terms with definition are unsupported.");
          }
        }

        out.append("(assert ");

        // This is the same as t.toString() does,
        // but directly uses the Appendable for better performance
        // and less memory consumption.
        Term letted = new FormulaLet().let(formula);
        termPrinter.append(out, letted);

        out.append(")");
      }
    };
  }

  @Override
  public Term simplify(Term pF) {
    SimplifyDDA s = new SimplifyDDA(getEnvironment(), true);
    return s.getSimplifiedTerm(pF);
  }
}
