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
import ap.parser.ISortedQuantified;
import ap.terfor.ConstantTerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.conjunctions.Quantifier.EX$;
import ap.types.Sort;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class PrincessQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final PrincessEnvironment env;

  PrincessQuantifiedFormulaManager(
      FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration>
          pCreator, LogManager pLogger) {
    super(pCreator, pLogger);
    env = getFormulaCreator().getEnv();
  }

  @Override
  public IExpression mkQuantifier(Quantifier q, List<IExpression> vars, IExpression body) {
    checkArgument(body instanceof IFormula);
    ap.terfor.conjunctions.Quantifier pq = (q == Quantifier.FORALL) ? ALL$.MODULE$ : EX$.MODULE$;
    if (vars.isEmpty()) {

      // Body already contains bound variables.
      return new ISortedQuantified(pq, PrincessEnvironment.INTEGER_SORT, (IFormula) body);
    } else {
      // TODO: add support for boolean quantification!
      return IExpression.quanConsts(pq, asScala(toConstantTerm(vars)), (IFormula) body);
    }
  }

  @Override
  public BooleanFormula mkWithoutQuantifier(
      Quantifier pQ,
      List<IExpression> pVariables,
      IExpression pBody) {
    throw new UnsupportedOperationException();
  }

  private List<ConstantTerm> toConstantTerm(List<IExpression> lst) {
    List<ConstantTerm> retVal = new ArrayList<>(lst.size());
    for (IExpression f : lst) {
      retVal.add(((IConstant) f).c());
    }
    return retVal;
  }

  @Override
  protected IExpression eliminateQuantifiers(IExpression formula)
      throws SolverException, InterruptedException {
    checkArgument(formula instanceof IFormula);
    return env.elimQuantifiers((IFormula) formula);
  }
}
