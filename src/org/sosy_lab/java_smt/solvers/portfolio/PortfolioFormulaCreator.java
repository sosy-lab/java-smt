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

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;
import java.util.logging.Level;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioArrayFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBitvectorFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioBooleanFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioEnumerationFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioFloatingPointFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioFloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioIntegerFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioRationalFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioRegexFormula;
import org.sosy_lab.java_smt.solvers.portfolio.PortfolioFormula.PortfolioStringFormula;

// TODO: this is more like the central control unit than a creator currently
// TODO: lift all helpful unified abstract implementations for TFormulaInfo into a new abstract
//  layer that portfolio AND all others can inherit

// For a full creator impl we need to hand through the solver specific elements, as they are
// returned in the public interfaces, otherwise we end up with solver specific types. But for
// example getBooleanVarDeclaration() does ONLY return solver specific types, hence we need the
// types of the nested creators!
// TFormulaInf would be Map<Solvers, ? extends Formula>
// TFuncDecl should be Map<Solvers, TFuncDecl> but TFuncDecl being the solver specific type! (Due
// to getBooleanVarDeclaration();) We could add a solver specific wrapper.
// TType maybe just FormulaType<?>? Unsure
// TEnv could either be Void or a controller for the portfolio (which solvers, remove/warnings
//  due to unsupported stuff etc.)
@SuppressWarnings("unchecked")
public class PortfolioFormulaCreator {

  // solversWithContexts is mutable to remove solvers that are not supposed to be used anymore to
  // build provers
  private final Map<Solvers, SolverContext> contexts;

  // We might remove solvers based on options
  private Map<Solvers, FormulaManager> formulaManagers;
  private Map<Solvers, UFManager> ufManagers;
  private Map<Solvers, BooleanFormulaManager> booleanManagers;
  private Map<Solvers, IntegerFormulaManager> integerManagers;
  private Map<Solvers, RationalFormulaManager> rationalManagers;
  private Map<Solvers, BitvectorFormulaManager> bitvectorManagers;
  private Map<Solvers, FloatingPointFormulaManager> floatingPointManagers;
  private Map<Solvers, QuantifiedFormulaManager> quantifiedManagers;
  private Map<Solvers, ArrayFormulaManager> arrayManagers;
  private Map<Solvers, SLFormulaManager> slManagers;
  private Map<Solvers, StringFormulaManager> stringManagers;
  private Map<Solvers, EnumerationFormulaManager> enumerationManagers;

  private final LogManager logger;

  private final boolean removeSolverFromPortfolioWhenUnsupported;

  // TODO: we implement the formula cache for multiple solvers -> generalize and offer common
  //  cache in optional abstract method implementation.
  public PortfolioFormulaCreator(
      Map<Solvers, SolverContext> pContexts,
      Map<Solvers, FormulaManager> pSolversToFormulaManagers,
      LogManager pLogger,
      boolean pRemoveSolverFromPortfolioWhenUnsupported)
      throws InvalidConfigurationException {
    removeSolverFromPortfolioWhenUnsupported = pRemoveSolverFromPortfolioWhenUnsupported;
    contexts = pContexts;
    formulaManagers = pSolversToFormulaManagers;
    // some manager maps might be smaller due to supported theories. We check them/throw them out
    // once used
    ufManagers = buildSupportedManager(formulaManagers, FormulaManager::getUFManager);
    booleanManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getBooleanFormulaManager);
    integerManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getIntegerFormulaManager);
    rationalManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getRationalFormulaManager);
    bitvectorManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getBitvectorFormulaManager);
    floatingPointManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getFloatingPointFormulaManager);
    quantifiedManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getQuantifiedFormulaManager);
    arrayManagers = buildSupportedManager(formulaManagers, FormulaManager::getArrayFormulaManager);
    slManagers = buildSupportedManager(formulaManagers, FormulaManager::getSLFormulaManager);
    stringManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getStringFormulaManager);
    enumerationManagers =
        buildSupportedManager(formulaManagers, FormulaManager::getEnumerationFormulaManager);

    if (contexts.size() != formulaManagers.size()) {
      throw new InvalidConfigurationException(
          "Error when building portfolio; more contexts than " + "managers");
    }
    logger = pLogger;
  }

  protected Map<Solvers, SolverContext> getSolverSpecificContexts() {
    return contexts;
  }

  protected Map<Solvers, FormulaManager> getSolverSpecificFormulaManagers() {
    return formulaManagers;
  }

  protected Map<Solvers, BooleanFormulaManager> getSolverSpecificBooleanFormulaManagers() {
    return booleanManagers;
  }

  protected Map<Solvers, UFManager> getSolverSpecificUfFormulaManagers() {
    return ufManagers;
  }

  protected Map<Solvers, IntegerFormulaManager> getSolverSpecificIntegerFormulaManagers() {
    return integerManagers;
  }

  protected Map<Solvers, RationalFormulaManager> getSolverSpecificRationalFormulaManagers() {
    return rationalManagers;
  }

  protected Map<Solvers, FloatingPointFormulaManager>
      getSolverSpecificFloatingPointFormulaManagers() {
    return floatingPointManagers;
  }

  protected Map<Solvers, ArrayFormulaManager> getSolverSpecificArrayFormulaManagers() {
    return arrayManagers;
  }

  protected Map<Solvers, QuantifiedFormulaManager> getSolverSpecificQuantifiedFormulaManagers() {
    return quantifiedManagers;
  }

  protected Map<Solvers, BitvectorFormulaManager> getSolverSpecificBitvectorFormulaManagers() {
    return bitvectorManagers;
  }

  protected Map<Solvers, StringFormulaManager> getSolverSpecificStringFormulaManagers() {
    return stringManagers;
  }

  protected Map<Solvers, EnumerationFormulaManager> getSolverSpecificEnumerationFormulaManagers() {
    return enumerationManagers;
  }

  protected Map<Solvers, SLFormulaManager> getSolverSpecificSlFormulaManagers() {
    return slManagers;
  }

  private static <FM> Map<Solvers, FM> buildSupportedManager(
      Map<Solvers, FormulaManager> managers, Function<FormulaManager, FM> getManager) {
    ImmutableMap.Builder<Solvers, FM> solversToManagersBuilder = ImmutableMap.builder();
    for (Entry<Solvers, FormulaManager> solverAndContext : managers.entrySet()) {
      try {
        FormulaManager fm = solverAndContext.getValue();
        solversToManagersBuilder.put(solverAndContext.getKey(), getManager.apply(fm));
      } catch (UnsupportedOperationException e) {
        // TODO: Add option
        // Ignore for now
      }
    }
    return solversToManagersBuilder.buildOrThrow();
  }

  /**
   * @param unsupportedMessage is put after: "The selected portfolio solvers do not support " and is
   *     ended with a dot.
   */
  protected void checkGetFormulaManager(
      Function<PortfolioFormulaCreator, Map<Solvers, ?>> getSolverSpecificManagers,
      String unsupportedMessage) {
    Map<Solvers, ?> managers = getSolverSpecificManagers.apply(this);
    if (managers.isEmpty()) {
      throw new UnsupportedOperationException(
          "The selected portfolio solvers do not support "
              + unsupportedMessage
              + ". Choose a different portfolio.");
    }
    if (managers.size() != contexts.size()) {
      // TODO: allow reduction of portfolio based on option
      String errorReason =
          "does not support "
              + unsupportedMessage
              + ". You can use "
              + "configuration option removeSolverFromPortfolioWhenUnsupported to adaptively "
              + "remove unsupported solvers from the portfolio.";
      for (Solvers notSupportingSolvers :
          contexts.keySet().stream()
              .filter(k -> !managers.containsKey(k))
              .collect(ImmutableSet.toImmutableSet())) {
        handleUnsupportedOperationWithReason(notSupportingSolvers, errorReason);
      }
    }
  }

  /**
   * Always use this if there is an error or unsupported operation for a solver to handle how the
   * portfolio responds to this.
   */
  protected void handleUnsupportedOperationWithReason(Solvers solver, String reason) {
    // solversWithContexts is mutable for removal in FormulaManager!
    // TODO: also handle open provers
    if (removeSolverFromPortfolioWhenUnsupported) {
      SolverContext context = contexts.get(solver);
      if (context != null) {
        formulaManagers =
            formulaManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        booleanManagers =
            booleanManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        integerManagers =
            integerManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        rationalManagers =
            rationalManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        arrayManagers =
            arrayManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        ufManagers =
            ufManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        floatingPointManagers =
            floatingPointManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        stringManagers =
            stringManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        slManagers =
            slManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        enumerationManagers =
            enumerationManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        bitvectorManagers =
            bitvectorManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        quantifiedManagers =
            quantifiedManagers.entrySet().stream()
                .filter(e -> e.getKey() != solver)
                .collect(ImmutableMap.toImmutableMap(Map.Entry::getKey, Map.Entry::getValue));
        // TODO: close all provers
        context.close();
        contexts.remove(solver);
      }

      if (contexts.isEmpty()) {
        throw new UnsupportedOperationException(
            "Last solver " + solver + " in portfolio removed due to: " + reason);
      }

      // TODO: show remaining solvers?
      logger.log(Level.WARNING, "Portfolio removed solver " + solver + " due to: " + reason);

    } else {
      throw new UnsupportedOperationException("Portfolio solver " + solver + " error: " + reason);
    }
  }

  public BooleanFormula encapsulateBoolean(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format("%s is not boolean type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioBooleanFormula(pTerm);
  }

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

  protected FloatingPointFormula encapsulateFloatingPoint(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format("%s is no FP type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioFloatingPointFormula(pTerm);
  }

  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Map<Solvers, ? extends Formula> pTerm,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format("%s is no array type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  protected StringFormula encapsulateString(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isStringType()
        : String.format("%s is no String type, but %s", pTerm, getFormulaType(pTerm));
    return new PortfolioStringFormula(pTerm);
  }

  protected RegexFormula encapsulateRegex(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isRegexType();
    return new PortfolioRegexFormula(pTerm);
  }

  protected EnumerationFormula encapsulateEnumeration(Map<Solvers, ? extends Formula> pTerm) {
    assert getFormulaType(pTerm).isEnumerationType();
    return new PortfolioEnumerationFormula(pTerm);
  }

  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((PortfolioArrayFormula<TI, TE>) pArray).getElementType();
  }

  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((PortfolioArrayFormula<TI, TE>) pArray).getIndexType();
  }

  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    return (FormulaType<T>) getFormulaType(((PortfolioFormula) pFormula).getFormulasPerSolver());
  }

  public <T extends Formula> FormulaType<T> getFormulaType(Map<Solvers, T> pFormula) {
    if (pFormula.isEmpty()) {
      throw new AssertionError("Empty set of portfolio formulas when accessing sort.");
    }
    FormulaType<?> resultType;
    Entry<Solvers, ? extends Formula> someSolverAndFormula = pFormula.entrySet().iterator().next();
    Solvers someSolver = someSolverAndFormula.getKey();
    Formula someFormula = someSolverAndFormula.getValue();

    FormulaManager specificManager = formulaManagers.get(someSolver);
    if (specificManager == null) {
      throw new AssertionError("Unknown solver in portfolio formula when accessing sort.");
    }

    resultType = specificManager.getFormulaType(someFormula);

    assert pFormula.entrySet().stream()
        .allMatch(
            e ->
                formulaManagers.get(e.getKey()) != null
                    && formulaManagers.get(e.getKey()).getFormulaType(e.getValue()) == resultType);

    return (FormulaType<T>) resultType;
  }

  public Formula encapsulateWithTypeOf(Map<Solvers, ? extends Formula> pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }

  @SuppressWarnings("unchecked")
  public <T extends Formula> T encapsulate(
      FormulaType<T> pType, Map<Solvers, ? extends Formula> pTerm) {
    checkArgument(
        pType.equals(getFormulaType(pTerm)),
        "Trying to encapsulate formula %s of type %s as %s",
        pTerm,
        getFormulaType(pTerm),
        pType);
    if (pType.isBooleanType()) {
      return (T) new PortfolioBooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new PortfolioIntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new PortfolioRationalFormula(pTerm);
    } else if (pType.isStringType()) {
      return (T) new PortfolioStringFormula(pTerm);
    } else if (pType.isRegexType()) {
      return (T) new PortfolioRegexFormula(pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) new PortfolioBitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new PortfolioFloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new PortfolioFloatingPointRoundingModeFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrayType = (ArrayFormulaType<?, ?>) pType;
      return (T) encapsulateArray(pTerm, arrayType.getIndexType(), arrayType.getElementType());
    } else if (pType.isEnumerationType()) {
      return (T) new PortfolioEnumerationFormula(pTerm);
    }
    throw new IllegalArgumentException(
        "Cannot create formulas of type " + pType + " in the  portfolio solver!");
  }

  // ######## Generic Function Calling Interfaces And Classes Below ########

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
          ImmutableMap.Builder<Solvers, RF> finalFormulaBuilder = ImmutableMap.builder();
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
          ManagerMap extends Map<Solvers, ManagerType>,
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
              ImmutableMap.Builder<Solvers, ReturnType> finalFormulaBuilder =
                  ImmutableMap.builder();
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
          ManagerMap extends Map<Solvers, Manager>,
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
              ImmutableMap.Builder<Solvers, ReturnType> finalFormulaBuilder =
                  ImmutableMap.builder();
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
