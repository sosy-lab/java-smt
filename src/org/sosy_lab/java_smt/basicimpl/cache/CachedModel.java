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

package org.sosy_lab.java_smt.basicimpl.cache;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

import java.math.BigInteger;
import java.util.Iterator;

import javax.annotation.Nullable;

/**
 * Model which stays alive in cache.
 */
class CachedModel implements Model {
  private final Model delegate;

  CachedModel(Model pDelegate) {
    delegate = pDelegate;
  }

  @Nullable
  @Override
  public Object evaluate(Formula f) {
    return delegate.evaluate(f);
  }

  @Nullable
  @Override
  public BigInteger evaluate(IntegerFormula f) {
    return delegate.evaluate(f);
  }

  @Nullable
  @Override
  public Rational evaluate(RationalFormula f) {
    return delegate.evaluate(f);
  }

  @Nullable
  @Override
  public Boolean evaluate(BooleanFormula f) {
    return delegate.evaluate(f);
  }

  @Nullable
  @Override
  public BigInteger evaluate(BitvectorFormula f) {
    return delegate.evaluate(f);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return delegate.iterator();
  }

  @Override
  public void close() {
    // Do nothing, as the model remains in cache.
  }
}
