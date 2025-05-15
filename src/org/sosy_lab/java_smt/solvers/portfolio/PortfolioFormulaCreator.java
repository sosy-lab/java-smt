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
import com.google.common.collect.ImmutableMap.Builder;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioArrayFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBitvectorFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioEnumerationFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioFloatingPointFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioIntegerFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioRegexFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioStringFormula;

public class PortfolioFormulaCreator
    extends FormulaCreator<Map<Solvers, ? extends Formula>, Void, Void, Void> {

  private final Map<Solvers, ? extends FormulaCreator<?, ?, ?, ?>> solversToCreators;
  private final Map<Solvers, ? extends FormulaManager> solversToManagers;

  public PortfolioFormulaCreator(
      Map<Solvers, ? extends FormulaCreator<?, ?, ?, ?>> pSolversToCreators,
      Map<Solvers, ? extends FormulaManager> pSolversToManagers) {
    super();
    solversToCreators = pSolversToCreators;
    solversToManagers = pSolversToManagers;
  }

  Map<Solvers, ? extends FormulaManager> getSolversToManagers() {
    return solversToManagers;
  }

  <T> Map<Solvers, T> getSpecializedManager(Function<FormulaManager, T> managerRetrieval) {

    ImmutableMap.Builder<Solvers, T> finalManagerBuilder = ImmutableMap.builder();
    for (Entry<Solvers, ? extends FormulaManager> solversAndManager :
        solversToManagers.entrySet()) {
      try {
        Solvers solver = solversAndManager.getKey();
        FormulaManager mgr = solversAndManager.getValue();
        T specializedManager = managerRetrieval.apply(mgr);
        if (specializedManager != null) {
          finalManagerBuilder.put(solver, specializedManager);
        }
      } catch (UnsupportedOperationException e) {
        // ignore, theory is not supported.
      }
    }

    Map<Solvers, T> finalManagers = finalManagerBuilder.buildOrThrow();
    if (finalManagers.isEmpty()) {
      throw new IllegalArgumentException(
          "The chosen portfolio of solvers does not support your "
              + "combination of theories or logics");
    }
    return finalManagers;
  }

  @Override
  public BooleanFormula encapsulateBoolean(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format("%s is not boolean type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioBooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : String.format("%s is no BV type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioBitvectorFormula(pTerm);
  }

  public IntegerFormula encapsulateInteger(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isIntegerType()
        : String.format("%s is no integer type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioIntegerFormula(pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format("%s is no FP type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioFloatingPointFormula(pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Map<Solvers, ? extends Formula> pTerm,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format("%s is no array type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  protected StringFormula encapsulateString(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isStringType()
        : String.format("%s is no String type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioStringFormula(pTerm);
  }

  @Override
  protected RegexFormula encapsulateRegex(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isRegexType();
    return new PortfolioRegexFormula(pTerm);
  }

  @Override
  protected EnumerationFormula encapsulateEnumeration(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isEnumerationType();
    return new PortfolioEnumerationFormula(pTerm);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((PortfolioArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((PortfolioArrayFormula<TI, TE>) pArray).getIndexType();
  }

  public FormulaType<?> getFormulaType(PortfolioFormula pFormula) {
    return getFormulaType(pFormula.getFormulasPerSolver());
  }

  @Override
  public FormulaType<?> getFormulaType(Map<Solvers, ? extends Formula> pFormula) {
    if (pFormula.isEmpty()) {
      throw new AssertionError("Empty set of portfolio formulas when accessing sort.");
    }
    FormulaType<?> resultType;
    Entry<Solvers, ? extends Formula> someSolverAndFormula = pFormula.entrySet().iterator().next();
    Solvers someSolver = someSolverAndFormula.getKey();
    Formula someFormula = someSolverAndFormula.getValue();

    FormulaManager specificManager = solversToManagers.get(someSolver);
    if (specificManager == null) {
      throw new AssertionError("Unknown solver in portfolio formula when accessing sort.");
    }

    resultType = specificManager.getFormulaType(someFormula);

    assert pFormula.entrySet().stream()
        .allMatch(
            e ->
                solversToManagers.get(e.getKey()) != null
                    && solversToManagers.get(e.getKey()).getFormulaType(e.getValue())
                        == resultType);
    return resultType;
  }

  @FunctionalInterface
  public interface ThreeParameterFunction<A1, A2, A3, R3> {
    R3 apply(A1 arg1, A2 arg2, A3 arg3);
  }

  @FunctionalInterface
  public interface FiveParameterFunction<
      InnerFunction extends ThreeParameterFunction<?, ?, ?, ?>,
      Arg1Type,
      Arg2Type,
      ManagerMap extends Map<Solvers, ?>,
      EncapsulationFunction,
      ReturnType> {
    ReturnType apply(
        InnerFunction innerFunction,
        Arg1Type arg1,
        Arg2Type arg2,
        ManagerMap managersMap,
        EncapsulationFunction encapsulationFunction);
  }

  @FunctionalInterface
  public interface FourParameterFunction<
      F2 extends TwoParameterFunction<?, ?, ?>, A1, MM extends Map<Solvers, ?>, EF, R3> {
    R3 apply(F2 innerFunction, A1 arg1, MM managersMap, EF encapsulationFunction);
  }

  @FunctionalInterface
  public interface ThreeParameterFunction2<
      F2 extends TwoParameterFunction<?, ?, ?>, A1, MM extends Map<Solvers, ?>, R3> {
    R3 apply(F2 function, A1 arg1, MM managersMap);
  }

  @FunctionalInterface
  public interface TwoParameterFunction<M, A extends Formula, R extends Formula> {
    R apply(M solverSpecificManager, A argument);
  }

  public abstract static class OneArgReturnFormulaInfo<
          F2 extends TwoParameterFunction<M, FS, RF>,
          A1,
          MM extends Map<Solvers, ?>,
          R3 extends Map<Solvers, RF>,
          M,
          FS extends Formula,
          RF extends Formula>
      implements ThreeParameterFunction2<F2, A1, MM, R3> {

    public ThreeParameterFunction2<F2, PortfolioFormula, Map<Solvers, M>, Map<Solvers, RF>> oneArg =
        (function, arg1, managersMap) -> {
          Builder<Solvers, RF> finalFormulaBuilder = ImmutableMap.builder();
          // Go by existing formula solver combinations as we might only have a subset of the
          // solvers
          // actually supporting the theory combination.
          for (Entry<Solvers, M> entry : managersMap.entrySet()) {
            Solvers solver = entry.getKey();
            M solverSpecificManager = entry.getValue();
            Formula specificF1 = arg1.getFormulasPerSolver().get(solver);
            if (specificF1 != null) {
              // Delegate to specific solver
              finalFormulaBuilder.put(
                  solver, function.apply(solverSpecificManager, (FS) specificF1));
            }
          }
          Map<Solvers, RF> finalTerm = finalFormulaBuilder.buildOrThrow();
          if (finalTerm.isEmpty()) {
            throw new IllegalArgumentException(
                "The chosen portfolio of solvers does not support your "
                    + "combination of theories or logics");
          }
          return finalTerm;
        };
  }

  public abstract static class OneArgReturnEncapsulated<
          InnerFunction extends TwoParameterFunction<ManagerType, InnerArg1, ReturnType>,
          Arg1Type,
          ManagerMap extends Map<Solvers, ?>,
          ManagerType,
          InnerArg1 extends Formula,
          EF extends Function<Map<Solvers, ? extends Formula>, ReturnType>,
          ReturnType extends Formula>
      implements FourParameterFunction<InnerFunction, Arg1Type, ManagerMap, EF, ReturnType> {

    public FourParameterFunction<
            InnerFunction,
            PortfolioFormula,
            Map<Solvers, ManagerType>,
            Function<Map<Solvers, ? extends Formula>, ReturnType>,
            ReturnType>
        oneArgReturnEncapsulated =
            (innerFunction, arg1, managersMap, encapsulationFunction) -> {
              Builder<Solvers, ReturnType> finalFormulaBuilder = ImmutableMap.builder();
              // Go by existing formula solver combinations as we might only have a subset of the
              // solvers
              // actually supporting the theory combination.
              for (Entry<Solvers, ManagerType> entry : managersMap.entrySet()) {
                Solvers solver = entry.getKey();
                ManagerType solverSpecificManager = entry.getValue();
                Formula specificF1 = arg1.getFormulasPerSolver().get(solver);
                if (specificF1 != null) {
                  // Delegate to specific solver
                  finalFormulaBuilder.put(
                      solver, innerFunction.apply(solverSpecificManager, (InnerArg1) specificF1));
                }
              }
              Map<Solvers, ? extends Formula> finalTerm = finalFormulaBuilder.buildOrThrow();
              if (finalTerm.isEmpty()) {
                throw new IllegalArgumentException(
                    "The chosen portfolio of solvers does not support your "
                        + "combination of theories or logics");
              }
              return encapsulationFunction.apply(finalTerm);
            };
  }

  public abstract static class TwoArgReturnEncapsulated<
          InnerFunction extends
              ThreeParameterFunction<Manager, InnerArg1Type, InnerArg2Type, ReturnType>,
          Arg1Type,
          Arg2Type,
          ManagerMap extends Map<Solvers, ?>,
          Manager,
          InnerArg1Type extends Formula,
          InnerArg2Type extends Formula,
          EncapsulationFunction extends Function<Map<Solvers, ? extends Formula>, ReturnType>,
          ReturnType extends Formula>
      implements FiveParameterFunction<
          InnerFunction, Arg1Type, Arg2Type, ManagerMap, EncapsulationFunction, ReturnType> {

    public FiveParameterFunction<
            InnerFunction,
            PortfolioFormula,
            PortfolioFormula,
            Map<Solvers, Manager>,
            Function<Map<Solvers, ? extends Formula>, ReturnType>,
            ReturnType>
        twoArgReturnEncapsulated =
            (innerFunction, arg1, arg2, managersMap, encapsulationFunction) -> {
              Builder<Solvers, ReturnType> finalFormulaBuilder = ImmutableMap.builder();
              // Go by existing formula solver combinations as we might only have a subset of the
              // solvers
              // actually supporting the theory combination.
              for (Entry<Solvers, Manager> entry : managersMap.entrySet()) {
                Solvers solver = entry.getKey();
                Manager solverSpecificManager = entry.getValue();
                Formula specificF1 = arg1.getFormulasPerSolver().get(solver);
                Formula specificF2 = arg2.getFormulasPerSolver().get(solver);
                if (specificF1 != null && specificF2 != null) {
                  // Delegate to specific solver
                  finalFormulaBuilder.put(
                      solver,
                      innerFunction.apply(
                          solverSpecificManager,
                          (InnerArg1Type) specificF1,
                          (InnerArg2Type) specificF2));
                }
              }
              Map<Solvers, ? extends Formula> finalTerm = finalFormulaBuilder.buildOrThrow();
              if (finalTerm.isEmpty()) {
                throw new IllegalArgumentException(
                    "The chosen portfolio of solvers does not support your "
                        + "combination of theories or logics");
              }
              return encapsulationFunction.apply(finalTerm);
            };
  }
}
