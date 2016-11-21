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

import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class CVC4Model extends CachingAbstractModel<Expr, Type, CVC4Environment>{

  // TODO: this will not work properly, as SmtEngine is affected by
  // added assertions.
  private final SmtEngine smtEngine;
  public Map<String, Object> evaluation;
//  private final ImmutableList<Expr> assertedFormulas;

  CVC4Model(CVC4FormulaCreator pCreator) {
    super(pCreator);
    this.smtEngine = pCreator.getSmtEngine();
    evaluation = new HashMap<String, Object>();
//    this.assertedFormulas = ImmutableList.copyOf(assertedFormulas);
  }

  @Override
  public Object evaluateImpl(Expr f) {
    return getValue(smtEngine.getValue(f));
  }



  public void createAllsatModel(
      SmtEngine smtEngine, Collection<Expr> assertedFormulas, CVC4FormulaCreator creator) {
    Collection<Expr> extracted = new HashSet<>();
    System.out.println("createAllsatModel 0");
    for (Expr expr : assertedFormulas) {
      extracted.addAll(creator.extractVariablesAndUFs(expr, true).values());
    }
    System.out.println("createAllsatModel 1");
    for (Expr lKeyTerm : extracted) {
      System.out.println("lKeyTerm = " + lKeyTerm);
      Expr lValueTerm = creator.getSmtEngine().getValue(lKeyTerm);
      Object lValue = getValue(lValueTerm);
      System.out.println("createAllsatModel 2");
      // Duplicate entries may occur if "uf(a)" and "uf(b)" occur in the formulas
      // and "a" and "b" have the same value, because "a" and "b" will both be resolved,
      // leading to two entries for "uf(1)" (if value is 1).
      Object existingValue = evaluation.get(lKeyTerm.toString());
      Verify.verify(
          existingValue == null || lValue.equals(existingValue),
          "Duplicate values for model entry %s: %s and %s",
          lKeyTerm,
          existingValue,
          lValue);
      evaluation.put(lKeyTerm.toString(), lValue);
    }
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
  public ImmutableList<ValueAssignment> modelToList() {
    // TODO Auto-generated method stub
    return null;
  }

  public static CVC4Model create(CVC4FormulaCreator pCreator) {
    return new CVC4Model(pCreator);
  }
}
