/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import com.google.common.collect.ImmutableMap;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class PortfolioBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Map<Solvers, ? extends Formula>, Void, Void, Void> {

  private final Map<Solvers, BooleanFormulaManager> managers;

  protected PortfolioBooleanFormulaManager(PortfolioFormulaCreator pCreator) {
    super(pCreator);
    managers = pCreator.getSpecializedManager(FormulaManager::getBooleanFormulaManager);
  }

  @Override
  protected Map<Solvers, ? extends Formula> makeVariableImpl(String pVar) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> entry1 : managers.entrySet()) {
      Solvers solver = entry1.getKey();
      BooleanFormulaManager mgr = entry1.getValue();
      finalFormulaBuilder.put(solver, mgr.makeVariable(pVar));
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> makeBooleanImpl(boolean value) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> entry1 : managers.entrySet()) {
      Solvers solver = entry1.getKey();
      BooleanFormulaManager mgr = entry1.getValue();
      finalFormulaBuilder.put(solver, mgr.makeBoolean(value));
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> not(Map<Solvers, ? extends Formula> pParam1) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> entry1 : pParam1.entrySet()) {
      Solvers solver = entry1.getKey();
      BooleanFormulaManager mgr = managers.get(solver);
      finalFormulaBuilder.put(solver, mgr.not((BooleanFormula) entry1.getValue()));
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> and(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> entry1 : pParam1.entrySet()) {
      Solvers solver = entry1.getKey();
      if (pParam2.containsKey(solver)) {
        BooleanFormulaManager mgr = managers.get(solver);
        finalFormulaBuilder.put(
            solver,
            mgr.and((BooleanFormula) entry1.getValue(), (BooleanFormula) pParam2.get(solver)));
      }
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> or(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> entry1 : pParam1.entrySet()) {
      Solvers solver = entry1.getKey();
      if (pParam2.containsKey(solver)) {
        BooleanFormulaManager mgr = managers.get(solver);
        finalFormulaBuilder.put(
            solver,
            mgr.or((BooleanFormula) entry1.getValue(), (BooleanFormula) pParam2.get(solver)));
      }
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> xor(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> entry1 : pParam1.entrySet()) {
      Solvers solver = entry1.getKey();
      if (pParam2.containsKey(solver)) {
        BooleanFormulaManager mgr = managers.get(solver);
        finalFormulaBuilder.put(
            solver,
            mgr.xor((BooleanFormula) entry1.getValue(), (BooleanFormula) pParam2.get(solver)));
      }
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected Map<Solvers, ? extends Formula> equivalence(
      Map<Solvers, ? extends Formula> bits1, Map<Solvers, ? extends Formula> bits2) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends Formula> entry1 : bits1.entrySet()) {
      Solvers solver = entry1.getKey();
      if (bits2.containsKey(solver)) {
        BooleanFormulaManager mgr = managers.get(solver);
        finalFormulaBuilder.put(
            solver,
            mgr.equivalence(
                (BooleanFormula) entry1.getValue(), (BooleanFormula) bits2.get(solver)));
      }
    }

    return finalFormulaBuilder.buildOrThrow();
  }

  @Override
  protected boolean isTrue(Map<Solvers, ? extends Formula> bits) {
    // TODO: query all and return fastest? seems overkill.
    Entry<Solvers, ? extends Formula> solversAndFormula = bits.entrySet().iterator().next();
    Solvers solver = solversAndFormula.getKey();
    BooleanFormulaManager mgr = managers.get(solver);
    boolean res = mgr.isTrue((BooleanFormula) solversAndFormula.getValue());
    assert bits.entrySet().stream()
        .allMatch(e -> managers.get(e.getKey()).isTrue((BooleanFormula) e.getValue()) == res);
    return res;
  }

  @Override
  protected boolean isFalse(Map<Solvers, ? extends Formula> bits) {
    // TODO: query all and return fastest? seems overkill.
    Entry<Solvers, ? extends Formula> solversAndFormula = bits.entrySet().iterator().next();
    Solvers solver = solversAndFormula.getKey();
    BooleanFormulaManager mgr = managers.get(solver);
    boolean res = mgr.isFalse((BooleanFormula) solversAndFormula.getValue());
    assert bits.entrySet().stream()
        .allMatch(e -> managers.get(e.getKey()).isFalse((BooleanFormula) e.getValue()) == res);
    return res;
  }

  @Override
  protected Map<Solvers, ? extends Formula> ifThenElse(
      Map<Solvers, ? extends Formula> cond,
      Map<Solvers, ? extends Formula> f1,
      Map<Solvers, ? extends Formula> f2) {
    ImmutableMap.Builder<Solvers, Formula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BooleanFormulaManager> solversAndManager : managers.entrySet()) {
      Solvers solver = solversAndManager.getKey();
      BooleanFormulaManager mgr = solversAndManager.getValue();
      Formula specF1 = f1.get(solver);
      Formula specCond = cond.get(solver);
      Formula specF2 = f2.get(solver);
      if (mgr != null && specF1 != null && specCond != null && specF2 != null) {
        finalFormulaBuilder.put(solver, mgr.ifThenElse((BooleanFormula) specCond, specF1, specF2));
      }
    }
    return finalFormulaBuilder.buildOrThrow();
  }
}
