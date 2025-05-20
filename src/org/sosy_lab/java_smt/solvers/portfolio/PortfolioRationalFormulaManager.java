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
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

@SuppressWarnings({"UnusedVariable"})
public class PortfolioRationalFormulaManager implements RationalFormulaManager {

  private final PortfolioFormulaCreator creator;
  private final NonLinearArithmetic nonLinearArithmetic;

  protected PortfolioRationalFormulaManager(
      PortfolioFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    creator = pCreator;
    nonLinearArithmetic = pNonLinearArithmetic;
  }

  private RationalFormula encapsulateRational(Map<Solvers, ? extends Formula> pTerm) {
    return creator.encapsulate(FormulaType.RationalType, pTerm);
  }

  @Override
  public RationalFormula makeNumber(long number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, RationalFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, RationalFormulaManager> solverAndMgr :
        creator.getSolverSpecificRationalFormulaManagers().entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      RationalFormulaManager mgr = solverAndMgr.getValue();
      // Delegate to specific solver
      finalFormulaBuilder.put(solver, mgr.makeNumber(number));
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
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula makeNumber(double number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula makeNumber(BigDecimal number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula makeNumber(String pI) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula makeNumber(Rational pRational) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula makeVariable(String pVar) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula negate(NumeralFormula number) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula add(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula sum(List<NumeralFormula> operands) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula subtract(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula divide(NumeralFormula numerator, NumeralFormula denominator) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public RationalFormula multiply(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula equal(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula distinct(List<NumeralFormula> pNumbers) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterThan(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula greaterOrEquals(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessThan(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula lessOrEquals(NumeralFormula number1, NumeralFormula number2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public IntegerFormula floor(NumeralFormula formula) {
    throw new UnsupportedOperationException("implement me");
  }
}
