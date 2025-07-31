// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static scala.collection.JavaConverters.asScala;

import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.terfor.ConstantTerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.conjunctions.Quantifier.EX$;
import ap.types.Sort;
import com.google.common.collect.Lists;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class PrincessQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final PrincessEnvironment env;

  PrincessQuantifiedFormulaManager(
      FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration>
          pCreator) {
    super(pCreator);
    env = getFormulaCreator().getEnv();
  }

  @Override
  public IExpression mkQuantifier(Quantifier q, List<IExpression> vars, IExpression body) {
    checkArgument(!vars.isEmpty(), "Missing variables for quantifier '%s' and body '%s'.", q, body);

    checkArgument(body instanceof IFormula);
    ap.terfor.conjunctions.Quantifier pq = (q == Quantifier.FORALL) ? ALL$.MODULE$ : EX$.MODULE$;

    // TODO: add support for boolean quantification!
    return IExpression.quanConsts(pq, asScala(toConstantTerms(vars)), (IFormula) body);
  }

  private List<ConstantTerm> toConstantTerms(List<IExpression> lst) {
    return Lists.transform(lst, f -> ((IConstant) f).c());
  }

  @Override
  protected IExpression eliminateQuantifiers(IExpression formula)
      throws SolverException, InterruptedException {
    checkArgument(formula instanceof IFormula);
    return env.elimQuantifiers((IFormula) formula);
  }
}
