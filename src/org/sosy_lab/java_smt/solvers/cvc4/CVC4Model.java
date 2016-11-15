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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

class CVC4Model extends AbstractModel<Expr, Type, CVC4Environment> {

  // TODO: this will not work properly, as SmtEngine is affected by
  // added assertions.
  private final SmtEngine smtEngine;
  private final ImmutableList<Expr> assertedFormulas;

  CVC4Model(
      SmtEngine smtEngine,
      FormulaCreator<Expr, Type, CVC4Environment, Expr> creator,
      Collection<Expr> assertedFormulas) {
    super(creator);
    this.smtEngine = smtEngine;
    this.assertedFormulas = ImmutableList.copyOf(assertedFormulas);
  }

  @Override
  public Object evaluateImpl(Expr f) {
    return getValue(smtEngine.getValue(f));
  }



  static Map<String, Object> createAllsatModel(
      SmtEngine smtEngine, Collection<Expr> assertedFormulas, CVC4FormulaCreator creator) {
    Map<String, Object> model = new LinkedHashMap<>();

    Collection<Expr> extracted = new HashSet<>();
    for (Expr expr : assertedFormulas) {
      extracted.addAll(creator.extractVariablesAndUFs(expr, true).values());
    }

    for (Expr lKeyTerm : extracted) {

      Expr lValueTerm = smtEngine.getValue(lKeyTerm);
      Object lValue = getValue(lValueTerm);

      // Duplicate entries may occur if "uf(a)" and "uf(b)" occur in the formulas
      // and "a" and "b" have the same value, because "a" and "b" will both be resolved,
      // leading to two entries for "uf(1)" (if value is 1).
      Object existingValue = model.get(lKeyTerm.toString());
      Verify.verify(
          existingValue == null || lValue.equals(existingValue),
          "Duplicate values for model entry %s: %s and %s",
          lKeyTerm,
          existingValue,
          lValue);
      model.put(lKeyTerm.toString(), lValue);
    }
    return model;
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
    } else {

      // String serialization for unknown terms.
      return value.toString();
    }
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub

  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    // TODO Auto-generated method stub
    return null;
  }

  public ImmutableList<ValueAssignment> modelToList() {
    // TODO Auto-generated method stub
    return null;
  }

  public static CVC4Model create(CVC4Environment pCvc4Env, long pCvc4Model,
      CVC4FormulaCreator pCreator) {
    // TODO Auto-generated method stub
    return null;
  }
}
