/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.cvc4;

import com.google.common.base.Verify;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.solver.AssignableTerm;
import org.sosy_lab.solver.AssignableTerm.Function;
import org.sosy_lab.solver.AssignableTerm.Variable;
import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.TermType;

import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

class CVC4Model {
  private CVC4Model() {}

  private static TermType getType(Expr t) {
    Type type = t.getType();
    if (type.isBoolean()) {
      return TermType.Boolean;
    } else if (type.isInteger()) {
      return TermType.Integer;
    } else if (type.isFloatingPoint()) {
      return TermType.FloatingPoint;
    }

    throw new IllegalArgumentException("Given sort cannot be converted to a TermType: " + type);
  }

  private static AssignableTerm toVariable(Expr t) {
    return new Variable(t.toString(), getType(t));
  }

  private static Function toFunction(Expr t, SmtEngine smtEngine) {
    String lName = t.getOperator().toString();
    TermType lType = getType(t);

    int lArity = (int) t.getNumChildren();

    Object[] lArguments = new Object[lArity];

    for (int lArgumentIndex = 0; lArgumentIndex < lArity; lArgumentIndex++) {
      Expr lArgument = t.getChild(lArgumentIndex);
      lArgument = smtEngine.getValue(lArgument);
      lArguments[lArgumentIndex] = getValue(lArgument);
    }

    return new Function(lName, lType, lArguments);
  }

  private static Object getValue(Expr value) {
    if (value.getType().isBoolean()) {
      return value.getConstBoolean();
    } else if (value.getType().isInteger() || value.getType().isFloatingPoint()) {
      Rational rat = value.getConstRational();
      if (rat.isIntegral()) {
        return new BigInteger(rat.getNumerator().toString());
      } else {
        return org.sosy_lab.common.rationals.Rational.of(
            new BigInteger(rat.getNumerator().toString()),
            new BigInteger(rat.getDenominator().toString()));
      }
    }

    throw new IllegalArgumentException("CVC4 model term with expected value " + value);
  }

  static Model createCVC4Model(SmtEngine smtEngine, Collection<Expr> assertedFormulas) {

    Map<AssignableTerm, Object> model = new LinkedHashMap<>();
    for (Expr lKeyTerm : CVC4Util.getVarsAndUIFs(assertedFormulas)) {
      Expr lValueTerm = smtEngine.getValue(lKeyTerm);

      AssignableTerm lAssignable;
      if (lKeyTerm.isVariable()) {
        lAssignable = toVariable(lKeyTerm);
      } else {
        lAssignable = toFunction(lKeyTerm, smtEngine);
      }

      Object lValue = getValue(lValueTerm);

      // Duplicate entries may occur if "uf(a)" and "uf(b)" occur in the formulas
      // and "a" and "b" have the same value, because "a" and "b" will both be resolved,
      // leading to two entries for "uf(1)" (if value is 1).
      Object existingValue = model.get(lAssignable);
      Verify.verify(
          existingValue == null || lValue.equals(existingValue),
          "Duplicate values for model entry %s: %s and %s",
          lAssignable,
          existingValue,
          lValue);
      model.put(lAssignable, lValue);
    }

    return new Model(model);
  }
}
