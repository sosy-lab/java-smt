/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.collect.ImmutableList;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedHashSet;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class CVC4Model extends CachingAbstractModel<Expr, Type, ExprManager> {

  private final ImmutableList<ValueAssignment> model;
  private final SmtEngine smtEngine;
  private final ImmutableList<Expr> assertedExpressions;

  CVC4Model(
      CVC4FormulaCreator pCreator, SmtEngine pSmtEngine, Collection<Expr> pAssertedExpressions) {
    super(pCreator);
    smtEngine = pSmtEngine;
    assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel();
  }

  @Override
  public Object evaluateImpl(Expr f) {
    return getValue(smtEngine.getValue(f));
  }

  private ImmutableList<ValueAssignment> generateModel() {
    Collection<Expr> extracted = new LinkedHashSet<>();
    for (Expr expr : assertedExpressions) {
      extracted.addAll(creator.extractVariablesAndUFs(expr, true).values());
    }

    ImmutableList.Builder<ValueAssignment> builder = ImmutableList.builder();
    for (Expr lKeyTerm : extracted) {
      builder.add(getAssignment(lKeyTerm));
    }
    return builder.build();
  }

  private static Object getValue(Expr value) {
    if (value.getType().isBoolean()) {
      return value.getConstBoolean();

    } else if (value.getType().isInteger()) {
      return new BigInteger(value.getConstRational().toString());

    } else if (value.getType().isReal()) {
      Rational rat = value.getConstRational();
      return org.sosy_lab.common.rationals.Rational.of(
          new BigInteger(rat.getNumerator().toString()),
          new BigInteger(rat.getDenominator().toString()));

    } else {
      // String serialization for unknown terms.
      return value.toString();
    }
  }

  private ValueAssignment getAssignment(Expr pKeyTerm) {
    Expr valueTerm = smtEngine.getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = getValue(valueTerm);
    return new ValueAssignment(
        keyFormula, valueFormula, equation, pKeyTerm.toString(), value, ImmutableList.of());
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub
  }

  @Override
  public ImmutableList<ValueAssignment> modelToList() {
    return model;
  }
}
