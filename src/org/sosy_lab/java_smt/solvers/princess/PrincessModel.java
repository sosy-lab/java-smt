// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.api.SimpleAPI;
import ap.basetypes.IdealInt;
import ap.parser.IBoolLit$;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntLit;
import ap.parser.IPlus;
import ap.parser.ITerm;
import ap.parser.ITimes;
import ap.theories.rationals.Rationals;
import ap.types.Sort;
import ap.types.Sort$;
import com.google.common.collect.ImmutableList;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class PrincessModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final PrincessAbstractProver<?> prover;

  private final ImmutableList<ValueAssignment> assignment;
  private final SimpleAPI api;

  // Keeps track of the temporary variables created for explicit term evaluations in the model.
  private int counter = 0;

  PrincessModel(
      FormulaManager pFormulaManager,
      PrincessAbstractProver<?> pProver,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator,
      SimpleAPI pApi) {
    super(pFormulaManager, pProver, creator);
    prover = pProver;
    api = pApi;

    assignment = super.asList();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return assignment;
  }

  /** Tries to determine the Sort of a Term. */
  private Sort getSort(IExpression pTerm) {
    // Just using sortof() won't work as Princess may have simplified the original term
    // FIXME: This may also affect other parts of the code that use sortof()
    if (pTerm instanceof ITimes) {
      ITimes times = (ITimes) pTerm;
      return getSort(times.subterm());
    } else if (pTerm instanceof IPlus) {
      IPlus plus = (IPlus) pTerm;
      return getSort(plus.apply(0));
    } else if (pTerm instanceof IFormula) {
      return creator.getBoolType();
    } else {
      // TODO: Do we need more cases?
      return Sort$.MODULE$.sortOf((ITerm) pTerm);
    }
  }

  /**
   * Simplify rational values.
   *
   * <p>Rewrite <code>a/1</code> as <code>a</code>, otherwise return the term unchanged
   */
  private ITerm simplifyRational(ITerm pTerm) {
    // TODO: Reduce the term further?
    // TODO: Also do this for the values in the model?
    if (Sort$.MODULE$.sortOf(pTerm).equals(creator.getRationalType())
        && pTerm instanceof IFunApp
        && ((IFunApp) pTerm).fun().name().equals("Rat_frac")
        && pTerm.apply(1).equals(new IIntLit(IdealInt.ONE()))) {
      return Rationals.int2ring((ITerm) pTerm.apply(0));
    }
    return pTerm;
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression expr) {
    // The utility variable only appears temporarily on the solver's stack.
    // The user should never notice it.
    // We might not even need an index/counter for the variable.
    String newVariable = "__JAVASMT__MODEL_EVAL_" + counter++;

    // Extending the partial model does not seem to work in Princess if the formula uses rational
    // variables. To work around this issue we (temporarily) add the formula to the assertion
    // stack and then repeat the sat-check to get the value.
    api.push();
    for (IFormula fixed : prover.getEvaluatedTerms()) {
      api.addAssertion(fixed);
    }

    if (expr instanceof ITerm) {
      ITerm term = (ITerm) expr;
      ITerm var = api.createConstant(newVariable, getSort(term));
      api.addAssertion(var.$eq$eq$eq(term));
      api.checkSat(true);
      ITerm value = simplifyRational(api.evalToTerm(var));
      api.pop();
      prover.addEvaluatedTerm(value.$eq$eq$eq(term));
      return value;
    } else {
      IFormula formula = (IFormula) expr;
      IFormula var = api.createBooleanVariable(newVariable);
      api.addAssertion(var.$less$eq$greater(formula));
      api.checkSat(true);
      IFormula value = IBoolLit$.MODULE$.apply(api.eval(var));
      api.pop();
      prover.addEvaluatedTerm(value.$less$eq$greater(formula));
      return value;
    }
  }
}
