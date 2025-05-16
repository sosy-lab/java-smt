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

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBitvectorFormula;

public class PortfolioBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Map<Solvers, ? extends Formula>, Void, Void, Void>
    implements BitvectorFormulaManager {

  private final Map<Solvers, BitvectorFormulaManager> managers;
  private final PortfolioFormulaCreator creator;
  private final PortfolioBooleanFormulaManager bmgr;

  protected PortfolioBitvectorFormulaManager(
      PortfolioFormulaCreator pCreator, PortfolioBooleanFormulaManager pBmgr) {
    super(pCreator, pBmgr);
    managers = pCreator.getSpecializedManager(FormulaManager::getBitvectorFormulaManager);
    creator = pCreator;
    bmgr = pBmgr;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.makeBitvector(length, pI));
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.makeBitvector(length, pI));
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> makeBitvectorImpl(int pLength, BigInteger pI) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.makeBitvector(length, pI));
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> makeBitvectorImpl(
      int length, Map<Solvers, ? extends Formula> pParam1) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    ImmutableMap.Builder<Solvers, IntegerFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.toIntegerFormula(pI, signed));
    }

    Map<Solvers, IntegerFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulate(FormulaType.IntegerType, finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> toIntegerFormulaImpl(
      Map<Solvers, ? extends Formula> pI, boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.makeVariable(length, pVar));
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> makeVariableImpl(int pLength, String pVar) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      finalTermBuilder.put(solver, specificBvMgr.makeVariable(type, pVar));
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public int getLength(BitvectorFormula number) {
    assert number instanceof PortfolioBitvectorFormula;
    Integer length = null;
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificFormula != null) {
        length = specificBvMgr.getLength(specificFormula);
        break;
      }
    }

    if (length == null) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    Integer finalLength = length;
    assert managers.entrySet().stream()
        .allMatch(
            e ->
                ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(e.getKey()) == null
                    || e.getValue()
                            .getLength(
                                ((PortfolioBitvectorFormula) number)
                                    .getFormulasPerSolver()
                                    .get(e.getKey()))
                        == finalLength);
    return length;
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    assert number instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificFormula != null) {
        finalTermBuilder.put(solver, specificBvMgr.negate(specificFormula));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> negate(Map<Solvers, ? extends Formula> pParam1) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.add(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> add(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.subtract(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> subtract(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    assert dividend instanceof PortfolioBitvectorFormula;
    assert divisor instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificDividend =
          ((PortfolioBitvectorFormula) dividend).getFormulasPerSolver().get(solver);
      BitvectorFormula specificDivisor =
          ((PortfolioBitvectorFormula) divisor).getFormulasPerSolver().get(solver);
      if (specificDividend != null && specificDivisor != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.divide(specificDividend, specificDivisor, signed));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> divide(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula smodulo(BitvectorFormula dividend, BitvectorFormula divisor) {
    assert dividend instanceof PortfolioBitvectorFormula;
    assert divisor instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificDividend =
          ((PortfolioBitvectorFormula) dividend).getFormulasPerSolver().get(solver);
      BitvectorFormula specificDivisor =
          ((PortfolioBitvectorFormula) divisor).getFormulasPerSolver().get(solver);
      if (specificDividend != null && specificDivisor != null) {
        finalTermBuilder.put(solver, specificBvMgr.smodulo(specificDividend, specificDivisor));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> smodulo(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula remainder(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    assert dividend instanceof PortfolioBitvectorFormula;
    assert divisor instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificDividend =
          ((PortfolioBitvectorFormula) dividend).getFormulasPerSolver().get(solver);
      BitvectorFormula specificDivisor =
          ((PortfolioBitvectorFormula) divisor).getFormulasPerSolver().get(solver);
      if (specificDividend != null && specificDivisor != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.remainder(specificDividend, specificDivisor, signed));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> remainder(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.multiply(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> multiply(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.equal(specificFormula1, specificFormula2));
      }
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
  protected Map<Solvers, ? extends Formula> equal(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.greaterThan(specificFormula1, specificFormula2, signed));
      }
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
  protected Map<Solvers, ? extends Formula> greaterThan(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.greaterOrEquals(specificFormula1, specificFormula2, signed));
      }
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
  protected Map<Solvers, ? extends Formula> greaterOrEquals(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.lessThan(specificFormula1, specificFormula2, signed));
      }
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
  protected Map<Solvers, ? extends Formula> lessThan(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assert number1 instanceof PortfolioBitvectorFormula;
    assert number2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) number1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) number2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.lessOrEquals(specificFormula1, specificFormula2, signed));
      }
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
  protected Map<Solvers, ? extends Formula> lessOrEquals(
      Map<Solvers, ? extends Formula> pParam1,
      Map<Solvers, ? extends Formula> pParam2,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    assert bits instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula =
          ((PortfolioBitvectorFormula) bits).getFormulasPerSolver().get(solver);
      if (specificFormula != null) {
        finalTermBuilder.put(solver, specificBvMgr.not(specificFormula));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }

    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> not(Map<Solvers, ? extends Formula> pParam1) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    assert bits1 instanceof PortfolioBitvectorFormula;
    assert bits2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) bits1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) bits2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.and(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> and(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    assert bits1 instanceof PortfolioBitvectorFormula;
    assert bits2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) bits1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) bits2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.or(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> or(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    assert bits1 instanceof PortfolioBitvectorFormula;
    assert bits2 instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificFormula1 =
          ((PortfolioBitvectorFormula) bits1).getFormulasPerSolver().get(solver);
      BitvectorFormula specificFormula2 =
          ((PortfolioBitvectorFormula) bits2).getFormulasPerSolver().get(solver);
      if (specificFormula1 != null && specificFormula2 != null) {
        finalTermBuilder.put(solver, specificBvMgr.xor(specificFormula1, specificFormula2));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> xor(
      Map<Solvers, ? extends Formula> pParam1, Map<Solvers, ? extends Formula> pParam2) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    assert number instanceof PortfolioBitvectorFormula;
    assert toShift instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      BitvectorFormula specificToShift =
          ((PortfolioBitvectorFormula) toShift).getFormulasPerSolver().get(solver);
      if (specificNumber != null && specificToShift != null) {
        finalTermBuilder.put(
            solver, specificBvMgr.shiftRight(specificNumber, specificToShift, signed));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> shiftRight(
      Map<Solvers, ? extends Formula> pNumber,
      Map<Solvers, ? extends Formula> toShift,
      boolean signed) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    assert number instanceof PortfolioBitvectorFormula;
    assert toShift instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      BitvectorFormula specificToShift =
          ((PortfolioBitvectorFormula) toShift).getFormulasPerSolver().get(solver);
      if (specificNumber != null && specificToShift != null) {
        finalTermBuilder.put(solver, specificBvMgr.shiftLeft(specificNumber, specificToShift));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> shiftLeft(
      Map<Solvers, ? extends Formula> pNumber, Map<Solvers, ? extends Formula> pToShift) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate) {
    assert number instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificNumber != null) {
        finalTermBuilder.put(solver, specificBvMgr.rotateLeft(specificNumber, toRotate));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate) {
    assert number instanceof PortfolioBitvectorFormula;
    assert toRotate instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      BitvectorFormula specificToRotate =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificNumber != null && specificToRotate != null) {
        finalTermBuilder.put(solver, specificBvMgr.rotateLeft(specificNumber, specificToRotate));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, int toRotate) {
    assert number instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificNumber != null) {
        finalTermBuilder.put(solver, specificBvMgr.rotateRight(specificNumber, toRotate));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate) {
    assert number instanceof PortfolioBitvectorFormula;
    assert toRotate instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      BitvectorFormula specificToRotate =
          ((PortfolioBitvectorFormula) toRotate).getFormulasPerSolver().get(solver);
      if (specificNumber != null && specificToRotate != null) {
        finalTermBuilder.put(solver, specificBvMgr.rotateRight(specificNumber, specificToRotate));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    assert prefix instanceof PortfolioBitvectorFormula;
    assert suffix instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificPrefix =
          ((PortfolioBitvectorFormula) prefix).getFormulasPerSolver().get(solver);
      BitvectorFormula specificSuffix =
          ((PortfolioBitvectorFormula) suffix).getFormulasPerSolver().get(solver);
      if (specificPrefix != null && specificSuffix != null) {
        finalTermBuilder.put(solver, specificBvMgr.concat(specificPrefix, specificSuffix));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> concat(
      Map<Solvers, ? extends Formula> number, Map<Solvers, ? extends Formula> pAppend) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    final int bitSize = getLength(number);
    checkArgument(0 <= lsb, "index out of bounds (negative index %s)", lsb);
    checkArgument(lsb <= msb, "invalid range (lsb %s larger than msb %s)", lsb, msb);
    checkArgument(msb < bitSize, "index out of bounds (index %s beyond length %s)", msb, bitSize);
    assert number instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificNumber != null) {
        finalTermBuilder.put(solver, specificBvMgr.extract(specificNumber, msb, lsb));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> extract(
      Map<Solvers, ? extends Formula> pNumber, int pMsb, int pLsb) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    checkArgument(0 <= extensionBits, "can not extend a negative number of bits");
    assert number instanceof PortfolioBitvectorFormula;
    ImmutableMap.Builder<Solvers, BitvectorFormula> finalTermBuilder = ImmutableMap.builder();
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      BitvectorFormula specificNumber =
          ((PortfolioBitvectorFormula) number).getFormulasPerSolver().get(solver);
      if (specificNumber != null) {
        finalTermBuilder.put(solver, specificBvMgr.extend(specificNumber, extensionBits, signed));
      }
    }

    Map<Solvers, BitvectorFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBitvector(finalTerm);
  }

  @Override
  protected Map<Solvers, ? extends Formula> extend(
      Map<Solvers, ? extends Formula> pNumber, int pExtensionBits, boolean pSigned) {
    throw new UnsupportedOperationException("Not implemented because calling method overridden");
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    // optimization
    if (pBits.size() <= 1) {
      return bmgr.makeTrue();
    } else if (pBits.size() > 1L << getLength(pBits.iterator().next())) {
      return bmgr.makeFalse();
    }

    ImmutableMap.Builder<Solvers, BooleanFormula> finalTermBuilder = ImmutableMap.builder();
    outer:
    for (Entry<Solvers, BitvectorFormulaManager> solverAndBvMgr : managers.entrySet()) {
      Solvers solver = solverAndBvMgr.getKey();
      BitvectorFormulaManager specificBvMgr = solverAndBvMgr.getValue();
      ImmutableList.Builder<BitvectorFormula> specificBitsBuilder = ImmutableList.builder();
      for (BitvectorFormula f : pBits) {
        BitvectorFormula specificBitv =
            ((PortfolioBitvectorFormula) f).getFormulasPerSolver().get(solver);
        if (specificBitv == null) {
          continue outer;
        }
        specificBitsBuilder.add(specificBitv);
      }
      List<BitvectorFormula> specificBits = specificBitsBuilder.build();

      finalTermBuilder.put(solver, specificBvMgr.distinct(specificBits));
    }

    Map<Solvers, BooleanFormula> finalTerm = finalTermBuilder.buildOrThrow();
    if (finalTerm.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return creator.encapsulateBoolean(finalTerm);
  }
}
