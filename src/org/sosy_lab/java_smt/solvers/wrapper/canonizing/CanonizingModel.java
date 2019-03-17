/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing;

import java.math.BigInteger;
import java.util.Iterator;
import javax.annotation.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

public class CanonizingModel implements Model {

  private static final long serialVersionUID = 1L;
  private final Model delegate;

  public CanonizingModel(Model pDelegate) {
    delegate = pDelegate;
  }

  @Override
  @Nullable
  public Object evaluate(Formula pF) {
    return delegate.evaluate(pF);
  }

  @Override
  @Nullable
  public BigInteger evaluate(IntegerFormula pF) {
    return delegate.evaluate(pF);
  }

  @Override
  @Nullable
  public Rational evaluate(RationalFormula pF) {
    return delegate.evaluate(pF);
  }

  @Override
  @Nullable
  public Boolean evaluate(BooleanFormula pF) {
    return delegate.evaluate(pF);
  }

  @Override
  @Nullable
  public BigInteger evaluate(BitvectorFormula pF) {
    return delegate.evaluate(pF);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return delegate.iterator();
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  @Nullable
  public <T extends Formula> T eval(T pFormula) {
    return delegate.eval(pFormula);
  }
}
