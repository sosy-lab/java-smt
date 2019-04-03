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
package org.sosy_lab.java_smt.solvers.wrapper.caching.prover;

import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.wrapper.caching.CacheableModel;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache;
import org.sosy_lab.java_smt.solvers.wrapper.caching.SMTCache.CachingMode;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormula;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaVisitor;

public abstract class AbstractCachingEnvironment<T> implements BasicProverEnvironment<T> {

  protected BooleanFormulaManager fmgr;
  protected SMTCache cache;
  protected BooleanFormula formula;
  protected final Deque<BooleanFormula> stack;
  protected @Nullable CanonizingFormulaVisitor visitor;
  private FormulaManager mgr;

  protected @Nullable Formula translated;

  public AbstractCachingEnvironment(
      FormulaManager pMgr,
      CachingMode pMode,
      Configuration config)
      throws InvalidConfigurationException {
    mgr = pMgr;
    fmgr = pMgr.getBooleanFormulaManager();
    cache = SMTCache.newSMTCache(pMode, config);

    formula = fmgr.makeTrue();
    stack = new ArrayDeque<>();
    stack.push(formula);
    visitor = new CanonizingFormulaVisitor(pMgr, new ArrayList<>());
  }

  protected abstract BasicProverEnvironment<T> getDelegate();

  @Override
  public void pop() {
    translated = null;
    formula = stack.pop();
    getDelegate().pop();
  }

  @Override
  @Nullable
  public T addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    translated = null;
    formula = fmgr.and(formula, pConstraint);
    return getDelegate().addConstraint(pConstraint);
  }

  @Override
  public void push() {
    translated = null;
    stack.push(formula);
    getDelegate().push();
  }

  protected Formula fromFormula(Formula pFormula) {
    if (visitor != null && !(pFormula instanceof CanonizingFormula)) {
      return visitor.translate(pFormula);
    }
    return pFormula;
  }

  protected Formula toFormula(Formula pFormula) {
    if (mgr != null && pFormula instanceof CanonizingFormula) {
      return ((CanonizingFormula) pFormula).toFormula(mgr);
    }
    return pFormula;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    Boolean cached = cache.isFormulaUnsat(translated);
    if (cached == null) {
      cached = getDelegate().isUnsat();
      cache.storeFormulaUnsat(translated, cached);
    }
    return cached;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    List<Formula> tAssumptions =
        translateCollectionFromFormula(pAssumptions);
    Boolean cached = cache.isFormulaUnsatWithAssumptions(translated, tAssumptions);
    if (cached == null) {
      cached = getDelegate().isUnsatWithAssumptions(pAssumptions);
      cache.storeFormulaUnsatWithAssumptions(translated, cached, tAssumptions);
    }
    return cached;
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    Model cached = cache.getFormulaModel(translated);
    if (cached == null) {
      boolean unsat = true;
      try {
        unsat = getDelegate().isUnsat();
      } catch (InterruptedException e) {
        throw new SolverException("Exception when trying to evaluate satisfiability.", e);
      }
      if (!unsat) {
        cached = new CacheableModel(mgr, getDelegate().getModel(), getDelegate());
        cache.storeFormulaModel(translated, cached);
      }
    } else {
      ((CacheableModel) cached).initialize(mgr, getDelegate());
    }
    return cached;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    ImmutableList<ValueAssignment> cached = cache.getFormulaModelAssignments(translated);
    if (cached == null) {
      boolean unsat = true;
      try {
        unsat = getDelegate().isUnsat();
      } catch (InterruptedException e) {
        throw new SolverException("Exception when trying to evaluate satisfiability.", e);
      }
      if (!unsat) {
        cached = getDelegate().getModelAssignments();
        cache.storeFormulaModelAssignments(translated, toCachedValueAssignments(cached));
      }
    } else {
      cached = fromCachedValueAssignments(cached);
    }
    return cached;
  }

  private ImmutableList<ValueAssignment>
      toCachedValueAssignments(ImmutableList<ValueAssignment> pCached) {
    List<ValueAssignment> transformed =
        pCached.asList().stream().map(va -> mapFromValueAssignment(va)).collect(
            Collectors.toList());
    return ImmutableList.copyOf(transformed);
  }

  private ValueAssignment mapFromValueAssignment(ValueAssignment pVa) {
    return new ValueAssignment(
        fromFormula(pVa.getKey()),
        fromFormula(pVa.getValueAsFormula()),
        (BooleanFormula) fromFormula(pVa.getAssignmentAsFormula()),
        pVa.getName(),
        pVa.getValue(),
        fromFormulasIfNecessary(pVa.getArgumentsInterpretation()));
  }

  private Collection<?> fromFormulasIfNecessary(ImmutableList<Object> pArgumentsInterpretation) {
    if (pArgumentsInterpretation == null) {
      return ImmutableList.copyOf(new ArrayList<String>());
    }
    if (pArgumentsInterpretation.isEmpty()
        || !(pArgumentsInterpretation.get(0) instanceof Formula)) {
      return ImmutableList.copyOf(pArgumentsInterpretation);
    }
    List<Formula> transformed =
        pArgumentsInterpretation.stream().map(ai -> fromFormula((Formula) ai)).collect(
            Collectors.toList());
    return ImmutableList.copyOf(transformed);
  }

  private ImmutableList<ValueAssignment>
      fromCachedValueAssignments(ImmutableList<ValueAssignment> pCached) {
    List<ValueAssignment> transformed =
        pCached.asList().stream().map(va -> mapToValueAssignment(va)).collect(Collectors.toList());
    return ImmutableList.copyOf(transformed);
  }

  private ValueAssignment mapToValueAssignment(ValueAssignment pVa) {
    return new ValueAssignment(
        toFormula(pVa.getKey()),
        toFormula(pVa.getValueAsFormula()),
        (BooleanFormula) toFormula(pVa.getAssignmentAsFormula()),
        pVa.getName(),
        pVa.getValue(),
        toFormulasIfNecessary(pVa.getArgumentsInterpretation()));
  }

  private Collection<?> toFormulasIfNecessary(ImmutableList<Object> pArgumentsInterpretation) {
    if (pArgumentsInterpretation == null) {
      return ImmutableList.copyOf(new ArrayList<String>());
    }
    if (pArgumentsInterpretation.isEmpty()
        || !(pArgumentsInterpretation.get(0) instanceof Formula)) {
      return ImmutableList.copyOf(pArgumentsInterpretation);
    }
    List<Formula> transformed =
        pArgumentsInterpretation.stream().map(ai -> toFormula((Formula) ai)).collect(
            Collectors.toList());
    return ImmutableList.copyOf(transformed);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    List<Formula> cached = cache.getFormulaUnsatCore(translated);
    List<BooleanFormula> computed;
    if (cached == null) {
      boolean unsat = true;
      try {
        unsat = getDelegate().isUnsat();
      } catch (InterruptedException | SolverException e) {
        throw new RuntimeException("Exception when trying to evaluate satisfiability.", e);
      }
      if (!unsat) {
        computed = getDelegate().getUnsatCore();
        cached = translateCollectionFromFormula(computed);
        cache.storeFormulaUnsatCore(translated, new ArrayList<>(cached));
      } else {
        computed = new ArrayList<>();
      }
    } else {
      computed = translateCollectionToFormula(cached, BooleanFormula.class);
    }
    return computed;
  }

  @Override
  public Optional<List<BooleanFormula>>
      unsatCoreOverAssumptions(Collection<BooleanFormula> pAssumptions)
          throws SolverException, InterruptedException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    List<Formula> tAssumptions =
        pAssumptions.stream().map(f -> fromFormula(f)).collect(Collectors.toList());
    Optional<List<BooleanFormula>> computed = Optional.empty();
    Optional<List<Formula>> cached =
        cache.getFormulaUnsatCoreOverAssumptions(translated, tAssumptions);
    if (cached == null || !cached.isPresent()) {
      boolean unsat = getDelegate().isUnsat();
      if (unsat) {
        computed = getDelegate().unsatCoreOverAssumptions(pAssumptions);
        cached =
            Optional
                .of(translateCollectionFromFormula(computed.get()));
        cache.storeFormulaUnsatCoreOverAssumptions(translated, cached, tAssumptions);
      }
    } else {
      computed =
          Optional.of(translateCollectionToFormula(cached.get(), BooleanFormula.class));
    }
    return computed;
  }

  @Override
  public void close() {
    getDelegate().close();
    cache.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    if (translated == null) {
      translated = fromFormula(formula);
    }
    List<Formula> cImportant = translateCollectionFromFormula(pImportant);

    List<List<BooleanFormula>> result = new ArrayList<>();
    List<List<Formula>> cached = cache.getAllSat(translated, cImportant);
    if (cached == null) {
      // calculate values
      result = getDelegate().allSat(new MyAllSatCallback(), pImportant);
      cached =
          result.stream().map(l -> translateCollectionFromFormula(l)).collect(Collectors.toList());
      cache.storeAllSat(translated, cImportant, cached);
    } else {
      result =
          cached.stream().map(l -> translateCollectionToFormula(l, BooleanFormula.class)).collect(
              Collectors.toList());
    }

    for (List<BooleanFormula> model : result) {
      pCallback.apply(model);
    }

    // return region of original callback
    return pCallback.getResult();
  }

  protected <F extends Formula> List<Formula>
      translateCollectionFromFormula(Collection<F> pCollection) {
    return pCollection.stream().map(f -> fromFormula(f)).collect(Collectors.toList());
  }

  @SuppressWarnings({"unchecked", "unused"})
  protected <F extends Formula> List<F>
      translateCollectionToFormula(Collection<Formula> pCollection, Class<F> pClazz) {
    return pCollection.stream().map(f -> (F) toFormula(f)).collect(Collectors.toList());
  }

  private class MyAllSatCallback implements AllSatCallback<List<List<BooleanFormula>>> {

    private List<List<BooleanFormula>> formulas = new ArrayList<>();

    @Override
    public void apply(List<BooleanFormula> pModel) {
      formulas.add(pModel);
    }

    @Override
    public List<List<BooleanFormula>> getResult() throws InterruptedException {
      return formulas;
    }
  }
}
