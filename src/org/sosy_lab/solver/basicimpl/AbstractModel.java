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
package org.sosy_lab.solver.basicimpl;

import com.google.common.base.Joiner;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

import java.math.BigInteger;

import javax.annotation.Nullable;

public abstract class AbstractModel<TFormulaInfo, TType, TEnv> implements Model {

  protected final FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator;

  protected AbstractModel(FormulaCreator<TFormulaInfo, TType, TEnv, ?> creator) {
    this.creator = creator;
  }

  @Nullable
  @Override
  public BigInteger evaluate(IntegerFormula f) {
    return (BigInteger) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public Rational evaluate(RationalFormula f) {
    return (Rational) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public Boolean evaluate(BooleanFormula f) {
    return (Boolean) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public BigInteger evaluate(BitvectorFormula f) {
    return (BigInteger) evaluateImpl(creator.extractInfo(f));
  }

  @Nullable
  @Override
  public final Object evaluate(Formula f) {
    return evaluateImpl(creator.extractInfo(f));
  }

  protected abstract Object evaluateImpl(TFormulaInfo f);

  @Override
  public String toString() {
    return Joiner.on('\n').join(iterator());
  }
}
