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
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

public class PortfolioRationalFormulaManager implements RationalFormulaManager {

  private final Map<Solvers, RationalFormulaManager> managers;
  private final PortfolioFormulaCreator creator;
  private final NonLinearArithmetic nonLinearArithmetic;

  PortfolioRationalFormulaManager(
      PortfolioFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    creator = pCreator;
    nonLinearArithmetic = pNonLinearArithmetic;
    managers = pCreator.getSpecializedManager(FormulaManager::getRationalFormulaManager);
  }

  private RationalFormula encapsulateRational(Map<Solvers, ? extends Formula> pTerm) {
    return creator.encapsulate(FormulaType.RationalType, pTerm);
  }

  @Override
  public RationalFormula makeNumber(long number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, RationalFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, RationalFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      RationalFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(number));
      }
    }

    Map<Solvers, RationalFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return encapsulateRational(finalFormula);
  }

  @Override
  public RationalFormula makeNumber(BigInteger number) {
    return null;
  }

  @Override
  public RationalFormula makeNumber(double number) {
    return null;
  }

  @Override
  public RationalFormula makeNumber(BigDecimal number) {
    return null;
  }

  @Override
  public RationalFormula makeNumber(String pI) {
    return null;
  }

  @Override
  public RationalFormula makeNumber(Rational pRational) {
    return null;
  }

  @Override
  public RationalFormula makeVariable(String pVar) {
    return null;
  }

  @Override
  public RationalFormula negate(NumeralFormula number) {
    return null;
  }

  @Override
  public RationalFormula add(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public RationalFormula sum(List<NumeralFormula> operands) {
    return null;
  }

  @Override
  public RationalFormula subtract(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public RationalFormula divide(NumeralFormula numerator, NumeralFormula denominator) {
    return null;
  }

  @Override
  public RationalFormula multiply(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula equal(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula distinct(List<NumeralFormula> pNumbers) {
    return null;
  }

  @Override
  public BooleanFormula greaterThan(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula greaterOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula lessThan(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public BooleanFormula lessOrEquals(NumeralFormula number1, NumeralFormula number2) {
    return null;
  }

  @Override
  public IntegerFormula floor(NumeralFormula formula) {
    return null;
  }
}
