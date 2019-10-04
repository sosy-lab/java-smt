/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.collect.Iterables.getOnlyElement;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class SmtInterpolFormulaManager
    extends AbstractFormulaManager<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> {

  SmtInterpolFormulaManager(
      SmtInterpolFormulaCreator pCreator,
      SmtInterpolUFManager pFunctionManager,
      SmtInterpolBooleanFormulaManager pBooleanManager,
      SmtInterpolIntegerFormulaManager pIntegerManager,
      SmtInterpolRationalFormulaManager pRationalManager,
      SmtInterpolArrayFormulaManager pArrayFormulaManager) {
    super(
        pCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        null,
        null,
        null,
        pArrayFormulaManager);
  }

  BooleanFormula encapsulateBooleanFormula(Term t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    Term term = getOnlyElement(getEnvironment().parseStringToTerms(pS));
    return encapsulateBooleanFormula(new FormulaUnLet().unlet(term));
  }

  @Override
  public Appender dumpFormula(final Term formula) {
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
  public <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor) {
    return getFormulaCreator().visit(f, rFormulaVisitor);
  }

  /** This method returns a 'shared' environment or a complete new environment. */
  SmtInterpolEnvironment createEnvironment() {
    return getEnvironment();
  }

  @Override
  public Term simplify(Term pF) {
    return getFormulaCreator().getEnv().simplify(pF);
  }
}
