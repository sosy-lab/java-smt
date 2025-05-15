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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioIntegerFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormulaCreator.OneArgReturnEncapsulated;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormulaCreator.ThreeParameterFunction;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormulaCreator.TwoArgReturnEncapsulated;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormulaCreator.TwoParameterFunction;

public class PortfolioIntegerFormulaManager implements IntegerFormulaManager {

  private final Map<Solvers, IntegerFormulaManager> managers;
  private final PortfolioFormulaCreator creator;
  private final NonLinearArithmetic nonLinearArithmetic;

  private final Function<Map<Solvers, ? extends Formula>, IntegerFormula> encapsulateInteger;

  private final Function<Map<Solvers, ? extends Formula>, BooleanFormula> encapsulateBoolean;

  PortfolioIntegerFormulaManager(
      PortfolioFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    creator = pCreator;
    nonLinearArithmetic = pNonLinearArithmetic;
    managers = pCreator.getSpecializedManager(FormulaManager::getIntegerFormulaManager);
    encapsulateInteger = creator::encapsulateInteger;
    encapsulateBoolean = creator::encapsulateBoolean;
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormula> entry1 :
        ((PortfolioIntegerFormula) number1).getFormulasPerSolver().entrySet()) {
      Solvers solver = entry1.getKey();
      IntegerFormula f2 = ((PortfolioIntegerFormula) number2).getFormulasPerSolver().get(solver);
      if (f2 != null) {
        IntegerFormulaManager mgr = managers.get(solver);
        if (mgr != null) {
          // Delegate to specific solver
          finalFormulaBuilder.put(solver, mgr.modularCongruence(entry1.getValue(), f2, n));
        }
      }
    }

    Map<Solvers, BooleanFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBoolean(finalFormula);
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, BooleanFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormula> entry1 :
        ((PortfolioIntegerFormula) number1).getFormulasPerSolver().entrySet()) {
      Solvers solver = entry1.getKey();
      IntegerFormula f2 = ((PortfolioIntegerFormula) number2).getFormulasPerSolver().get(solver);
      if (f2 != null) {
        IntegerFormulaManager mgr = managers.get(solver);
        if (mgr != null) {
          // Delegate to specific solver
          finalFormulaBuilder.put(solver, mgr.modularCongruence(entry1.getValue(), f2, n));
        }
      }
    }

    Map<Solvers, BooleanFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBoolean(finalFormula);
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
        apply = IntegerFormulaManager::modulo;

    return twoIntArgRetInt.apply(
        apply,
        (PortfolioIntegerFormula) numerator,
        (PortfolioIntegerFormula) denominator,
        managers,
        encapsulateInteger);
  }

  @Override
  public IntegerFormula makeNumber(long number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(number));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeNumber(BigInteger number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(number));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeNumber(double number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(number));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeNumber(BigDecimal number) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(number));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeNumber(String pI) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(pI));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeNumber(Rational pRational) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeNumber(pRational));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula makeVariable(String pVar) {
    // Go by existing formula solver combinations as we might only have a subset of the solvers
    // actually supporting the theory combination.
    ImmutableMap.Builder<Solvers, IntegerFormula> finalFormulaBuilder = ImmutableMap.builder();
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager mgr = solverAndMgr.getValue();
      if (mgr != null) {
        // Delegate to specific solver
        finalFormulaBuilder.put(solver, mgr.makeVariable(pVar));
      }
    }

    Map<Solvers, IntegerFormula> finalFormula = finalFormulaBuilder.buildOrThrow();
    if (finalFormula.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalFormula);
  }

  @Override
  public IntegerFormula negate(IntegerFormula number) {
    TwoParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula> apply =
        NumeralFormulaManager::negate;

    return oneIntArgRetInt.apply(
        apply, (PortfolioIntegerFormula) number, managers, encapsulateInteger);
  }

  @Override
  public IntegerFormula add(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
        apply = NumeralFormulaManager::add;

    return twoIntArgRetInt.apply(
        apply,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateInteger);
  }

  @Override
  public IntegerFormula sum(List<IntegerFormula> operands) {
    ImmutableMap.Builder<Solvers, IntegerFormula> finalTermBuilder = ImmutableMap.builder();
    outer:
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager specificMgr = solverAndMgr.getValue();
      ImmutableList.Builder<IntegerFormula> specificOperandsBuilder = ImmutableList.builder();
      for (IntegerFormula f : operands) {
        IntegerFormula specificOperands =
            ((PortfolioIntegerFormula) f).getFormulasPerSolver().get(solver);
        if (specificOperands == null) {
          continue outer;
        }
        specificOperandsBuilder.add(specificOperands);
      }
      List<IntegerFormula> specificOperands = specificOperandsBuilder.build();

      finalTermBuilder.put(solver, specificMgr.sum(specificOperands));
    }

    Map<Solvers, IntegerFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateInteger(finalTerm);
  }

  @Override
  public IntegerFormula subtract(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
        apply = NumeralFormulaManager::subtract;

    return twoIntArgRetInt.apply(
        apply,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateInteger);
  }

  @Override
  public IntegerFormula divide(IntegerFormula numerator, IntegerFormula denominator) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
        apply = NumeralFormulaManager::divide;

    return twoIntArgRetInt.apply(
        apply,
        (PortfolioIntegerFormula) numerator,
        (PortfolioIntegerFormula) denominator,
        managers,
        encapsulateInteger);
  }

  @Override
  public IntegerFormula multiply(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
        apply = NumeralFormulaManager::multiply;

    return twoIntArgRetInt.apply(
        apply,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateInteger);
  }

  @Override
  public BooleanFormula equal(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
        apply = NumeralFormulaManager::equal;

    return twoIntArgRetBool.apply(
        apply,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateBoolean);
  }

  @Override
  public BooleanFormula distinct(List<IntegerFormula> pNumbers) {
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    outer:
    for (Entry<Solvers, IntegerFormulaManager> solverAndMgr : managers.entrySet()) {
      Solvers solver = solverAndMgr.getKey();
      IntegerFormulaManager specificMgr = solverAndMgr.getValue();
      ImmutableList.Builder<IntegerFormula> specificNumbersBuilder = ImmutableList.builder();
      for (IntegerFormula f : pNumbers) {
        IntegerFormula specificNumber =
            ((PortfolioIntegerFormula) f).getFormulasPerSolver().get(solver);
        if (specificNumber == null) {
          continue outer;
        }
        specificNumbersBuilder.add(specificNumber);
      }
      List<IntegerFormula> specificNumbers = specificNumbersBuilder.build();

      finalTermBuilder.put(solver, specificMgr.distinct(specificNumbers));
    }

    Map<Solvers, BooleanFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBoolean(finalTerm);
  }

  @Override
  public BooleanFormula greaterThan(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
        applyGreaterThan = NumeralFormulaManager::greaterThan;

    return twoIntArgRetBool.apply(
        applyGreaterThan,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateBoolean);
  }

  @Override
  public BooleanFormula greaterOrEquals(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
        applyGreaterOrEquals = NumeralFormulaManager::greaterOrEquals;

    return twoIntArgRetBool.apply(
        applyGreaterOrEquals,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateBoolean);
  }

  @Override
  public BooleanFormula lessThan(IntegerFormula number1, IntegerFormula number2) {
    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
        applyLessThan = NumeralFormulaManager::lessThan;

    return twoIntArgRetBool.apply(
        applyLessThan,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateBoolean);
  }

  @Override
  public BooleanFormula lessOrEquals(IntegerFormula number1, IntegerFormula number2) {
    assert number1 instanceof PortfolioIntegerFormula;
    assert number2 instanceof PortfolioIntegerFormula;

    ThreeParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
        applyLessOrEquals = NumeralFormulaManager::lessOrEquals;

    return twoIntArgRetBool.apply(
        applyLessOrEquals,
        (PortfolioIntegerFormula) number1,
        (PortfolioIntegerFormula) number2,
        managers,
        encapsulateBoolean);
  }

  @Override
  public IntegerFormula floor(IntegerFormula formula) {
    assert formula instanceof PortfolioIntegerFormula;

    TwoParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula> applyFloor =
        NumeralFormulaManager::floor;

    return oneIntArgRetInt.apply(
        applyFloor, (PortfolioIntegerFormula) formula, managers, encapsulateInteger);
  }

  private final OneArgReturnEncapsulated<
          TwoParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula>,
          PortfolioIntegerFormula,
          Map<Solvers, IntegerFormulaManager>,
          IntegerFormulaManager,
          IntegerFormula,
          Function<Map<Solvers, ? extends Formula>, IntegerFormula>,
          IntegerFormula>
      oneIntArgRetInt =
          new OneArgReturnEncapsulated<>() {
            @Override
            public IntegerFormula apply(
                TwoParameterFunction<IntegerFormulaManager, IntegerFormula, IntegerFormula>
                    innerFunction,
                PortfolioIntegerFormula arg1,
                Map<Solvers, IntegerFormulaManager> managersMap,
                Function<Map<Solvers, ? extends Formula>, IntegerFormula> encapsulateInteger) {
              return oneArgReturnEncapsulated.apply(
                  innerFunction, arg1, managers, encapsulateInteger);
            }
          };

  private final TwoArgReturnEncapsulated<
          ThreeParameterFunction<
              IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>,
          PortfolioIntegerFormula,
          PortfolioIntegerFormula,
          Map<Solvers, IntegerFormulaManager>,
          IntegerFormulaManager,
          IntegerFormula,
          IntegerFormula,
          Function<Map<Solvers, ? extends Formula>, BooleanFormula>,
          BooleanFormula>
      twoIntArgRetBool =
          new TwoArgReturnEncapsulated<>() {
            @Override
            public BooleanFormula apply(
                ThreeParameterFunction<
                        IntegerFormulaManager, IntegerFormula, IntegerFormula, BooleanFormula>
                    innerFunction,
                PortfolioIntegerFormula arg1,
                PortfolioIntegerFormula arg2,
                Map<Solvers, IntegerFormulaManager> managersMap,
                Function<Map<Solvers, ? extends Formula>, BooleanFormula> encapsulate) {
              return twoArgReturnEncapsulated.apply(
                  innerFunction, arg1, arg2, managers, encapsulateBoolean);
            }
          };

  private final TwoArgReturnEncapsulated<
          ThreeParameterFunction<
              IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>,
          PortfolioIntegerFormula,
          PortfolioIntegerFormula,
          Map<Solvers, IntegerFormulaManager>,
          IntegerFormulaManager,
          IntegerFormula,
          IntegerFormula,
          Function<Map<Solvers, ? extends Formula>, IntegerFormula>,
          IntegerFormula>
      twoIntArgRetInt =
          new TwoArgReturnEncapsulated<>() {
            @Override
            public IntegerFormula apply(
                ThreeParameterFunction<
                        IntegerFormulaManager, IntegerFormula, IntegerFormula, IntegerFormula>
                    innerFunction,
                PortfolioIntegerFormula arg1,
                PortfolioIntegerFormula arg2,
                Map<Solvers, IntegerFormulaManager> managersMap,
                Function<Map<Solvers, ? extends Formula>, IntegerFormula> encapsulateInteger) {
              return twoArgReturnEncapsulated.apply(
                  innerFunction, arg1, arg2, managers, encapsulateInteger);
            }
          };
}
