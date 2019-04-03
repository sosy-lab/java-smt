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
package org.sosy_lab.java_smt.solvers.wrapper.caching;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormula;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaVisitor;

public class CacheableModel implements Model {

  private static final long serialVersionUID = 1L;

  private transient @Nullable CanonizingFormulaVisitor visitor;
  private transient @Nullable FormulaManager mgr;
  private transient @Nullable Model delegate;
  private transient @Nullable BasicProverEnvironment<?> fallback;

  private Map<Formula, Formula> evalMap = new HashMap<>();

  private Map<Formula, Object> evaluateMap = new HashMap<>();

  private ImmutableList<ValueAssignment> list;

  public CacheableModel(FormulaManager pMgr, Model pDelegate, BasicProverEnvironment<?> pFallback) {
    visitor = new CanonizingFormulaVisitor(pMgr, new ArrayList<>());
    mgr = pMgr;
    delegate = pDelegate;
    fallback = pFallback;
  }

  public void initialize(FormulaManager pMgr, BasicProverEnvironment<?> pFallback) {
    mgr = pMgr;
    visitor = new CanonizingFormulaVisitor(mgr, new ArrayList<>());
    fallback = pFallback;
  }

  public void setDelegate(Model pDelegate) {
    delegate = pDelegate;
  }

  private Formula fromFormula(Formula pFormula) {
    Formula translated = pFormula;
    if (visitor != null) {
      translated = visitor.translate(pFormula);
    }
    return translated;
  }

  private Formula toFormula(Formula pFormula) {
    Formula translated = pFormula;
    if (mgr != null && pFormula instanceof CanonizingFormula) {
      translated = ((CanonizingFormula) pFormula).toFormula(mgr);
    }
    return translated;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> @Nullable T
      eval(T pFormula) {
    Formula key = fromFormula(pFormula);
    if (delegate != null) {
      evalMap.computeIfAbsent(key, o -> fromFormula(delegate.eval(pFormula)));
    } else if (fallback != null) {
      evalMap.computeIfAbsent(key, o -> {
        // XXX: possibly unsafe
        try {
          fallback.isUnsat();
          return fromFormula(fallback.getModel().eval(pFormula));
        } catch (SolverException | InterruptedException e) {
          throw new RuntimeException("Error during uncached Model-Computation.", e);
        }
      });
    }
    return (T) toFormula(evalMap.get(key));
  }

  @SuppressWarnings("unchecked")
  public <T extends Formula> T storeEval(T pFormula, T result) {
    Formula key = fromFormula(pFormula);
    Formula value = fromFormula(result);
    evalMap.putIfAbsent(key, value);
    return (T) toFormula(evalMap.get(key));
  }

  @Override
  public @Nullable Object evaluate(Formula pF) {
    Formula key = fromFormula(pF);
    if (delegate != null) {
      evaluateMap.computeIfAbsent(key, o -> delegate.evaluate(pF));
    } else if (fallback != null) {
      evaluateMap.computeIfAbsent(key, o -> {
        // XXX: possibly unsafe
        try {
          fallback.isUnsat();
          return fallback.getModel().evaluate(pF);
        } catch (SolverException | InterruptedException e) {
          throw new RuntimeException("Error during uncached Model-Computation.", e);
        }
      });
    }
    return evaluateMap.get(key);
  }

  public Object storeEvaluate(Formula pF, Object result) {
    Formula key = fromFormula(pF);
    evaluateMap.putIfAbsent(key, result);
    return evaluateMap.get(key);
  }

  @Override
  public @Nullable BigInteger
      evaluate(IntegerFormula pF) {
    return (BigInteger) evaluate((Formula) pF);
  }

  @Override
  public @Nullable Rational
      evaluate(RationalFormula pF) {
    return (Rational) evaluate((Formula) pF);
  }

  @Override
  public @Nullable Boolean evaluate(BooleanFormula pF) {
    return (Boolean) evaluate((Formula) pF);
  }

  @Override
  public @Nullable BigInteger
      evaluate(BitvectorFormula pF) {
    return (BigInteger) evaluate((Formula) pF);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    if (list == null && delegate != null) {
      list = delegate.asList();
    }
    return list;
  }

  public void storeList(ImmutableList<ValueAssignment> pList) {
    list = pList;
  }

  @Override
  public void close() {
    if (delegate != null) {
      delegate.close();
    }
  }
}
