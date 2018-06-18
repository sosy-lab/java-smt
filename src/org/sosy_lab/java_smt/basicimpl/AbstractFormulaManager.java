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
package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.CharMatcher;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.tactics.NNFVisitor;
import org.sosy_lab.java_smt.utils.SolverUtils;

/**
 * Simplifies building a solver from the specific theories.
 *
 * @param <TFormulaInfo> The solver specific type.
 */
public abstract class AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements FormulaManager {

  /**
   * Avoid using basic mathematical or logical operators of SMT-LIB2 as names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  @VisibleForTesting
  public static final ImmutableSet<String> BASIC_OPERATORS =
      ImmutableSet.of("!", "+", "-", "*", "/", "%", "=", "<", ">", "<=", ">=");

  /**
   * Avoid using basic keywords of SMT-LIB2 as names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  @VisibleForTesting
  public static final ImmutableSet<String> SMTLIB2_KEYWORDS =
      ImmutableSet.of("true", "false", "and", "or", "select", "store", "xor", "distinct");

  /**
   * Avoid using escape characters of SMT-LIB2 as part of names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  static final CharMatcher DISALLOWED_CHARACTERS = CharMatcher.anyOf("|\\");

  private final @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      arrayManager;

  private final AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> booleanManager;

  private final @Nullable IntegerFormulaManager integerManager;

  private final @Nullable RationalFormulaManager rationalManager;

  private final @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      bitvectorManager;

  private final @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      floatingPointManager;

  private final AbstractUFManager<TFormulaInfo, ?, TType, TEnv> functionManager;

  private final @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      quantifiedManager;

  private final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator;

  /** Builds a solver from the given theory implementations */
  @SuppressWarnings("checkstyle:parameternumber")
  protected AbstractFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator,
      AbstractUFManager<TFormulaInfo, ?, TType, TEnv> functionManager,
      AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> booleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable
          AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> bitvectorManager,
      @Nullable
          AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
              floatingPointManager,
      @Nullable
          AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> quantifiedManager,
      @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> arrayManager) {

    this.arrayManager = arrayManager;
    this.quantifiedManager = quantifiedManager;
    this.functionManager = checkNotNull(functionManager, "function manager needed");
    this.booleanManager = checkNotNull(booleanManager, "boolean manager needed");
    this.integerManager = pIntegerManager;
    this.rationalManager = pRationalManager;
    this.bitvectorManager = bitvectorManager;
    this.floatingPointManager = floatingPointManager;
    this.formulaCreator = pFormulaCreator;

    if (booleanManager.getFormulaCreator() != formulaCreator
        || functionManager.getFormulaCreator() != formulaCreator
        || (bitvectorManager != null && bitvectorManager.getFormulaCreator() != formulaCreator)
        || (floatingPointManager != null
            && floatingPointManager.getFormulaCreator() != formulaCreator)) {
      throw new IllegalArgumentException("The creator instances must match across the managers!");
    }
  }

  public final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> getFormulaCreator() {
    return formulaCreator;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    if (integerManager == null) {
      throw new UnsupportedOperationException("Solver does not support integer theory");
    }
    return integerManager;
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    if (rationalManager == null) {
      throw new UnsupportedOperationException("Solver does not support rationals theory");
    }
    return rationalManager;
  }

  @Override
  public AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getBooleanFormulaManager() {
    return booleanManager;
  }

  @Override
  public AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getBitvectorFormulaManager() {
    if (bitvectorManager == null) {
      throw new UnsupportedOperationException("Solver does not support bitvector theory");
    }
    return bitvectorManager;
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    if (floatingPointManager == null) {
      throw new UnsupportedOperationException("Solver does not support floating point theory");
    }
    return floatingPointManager;
  }

  @Override
  public AbstractUFManager<TFormulaInfo, ?, TType, TEnv> getUFManager() {
    return functionManager;
  }

  @Override
  public AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getQuantifiedFormulaManager() {
    if (quantifiedManager == null) {
      throw new UnsupportedOperationException("Solver does not support quantification");
    }
    return quantifiedManager;
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    if (arrayManager == null) {
      throw new UnsupportedOperationException("Solver does not support arrays");
    }
    return arrayManager;
  }

  public abstract Appender dumpFormula(TFormulaInfo t);

  @Override
  public Appender dumpFormula(BooleanFormula t) {
    return dumpFormula(formulaCreator.extractInfo(t));
  }

  @Override
  public final <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return formulaCreator.getFormulaType(checkNotNull(formula));
  }

  // Utility methods that are handy for subclasses

  public final TEnv getEnvironment() {
    return getFormulaCreator().getEnv();
  }

  public final TFormulaInfo extractInfo(Formula f) {
    return formulaCreator.extractInfo(f);
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula f, Tactic tactic) throws InterruptedException {
    switch (tactic) {
      case ACKERMANNIZATION:
        return applyUFEImpl(f);
      case NNF:
        return applyNNFImpl(f);
      case TSEITIN_CNF:
        return applyCNFImpl(f);
      case QE_LIGHT:
        return applyQELightImpl(f);
      default:
        throw new UnsupportedOperationException("Unexpected enum value");
    }
  }

  /**
   * @param pF Input to apply the UFE transformation to.
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyUFEImpl(BooleanFormula pF) throws InterruptedException {
    return SolverUtils.ufElimination(this).eliminateUfs(pF);
  }

  /** @throws InterruptedException Can be thrown by the native code. */
  protected BooleanFormula applyQELightImpl(BooleanFormula pF) throws InterruptedException {

    // Returning the untouched formula is valid according to QE_LIGHT contract.
    // TODO: substitution-based implementation.
    return pF;
  }

  /**
   * @param pF Input to apply the CNF transformation to.
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyCNFImpl(BooleanFormula pF) throws InterruptedException {

    // TODO: generic implementation.
    throw new UnsupportedOperationException(
        "Currently there is no generic implementation for CNF conversion");
  }

  /** @throws InterruptedException Can be thrown by the native code. */
  protected BooleanFormula applyNNFImpl(BooleanFormula input) throws InterruptedException {
    return getBooleanFormulaManager().transformRecursively(input, new NNFVisitor(this));
  }

  @Override
  public <T extends Formula> T simplify(T f) throws InterruptedException {
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), simplify(extractInfo(f)));
  }

  /** @throws InterruptedException Can be thrown by the native code. */
  protected TFormulaInfo simplify(TFormulaInfo f) throws InterruptedException {
    return f;
  }

  @Override
  public <R> R visit(Formula input, FormulaVisitor<R> visitor) {
    return formulaCreator.visit(input, visitor);
  }

  @Override
  public void visitRecursively(Formula pF, FormulaVisitor<TraversalProcess> pFormulaVisitor) {
    formulaCreator.visitRecursively(pFormulaVisitor, pF);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return formulaCreator.transformRecursively(pFormulaVisitor, f);
  }

  /**
   * Extract names of all free variables in a formula.
   *
   * @param f The input formula
   */
  @Override
  public Map<String, Formula> extractVariables(Formula f) {
    ImmutableMap.Builder<String, Formula> found = ImmutableMap.builder();
    formulaCreator.extractVariablesAndUFs(f, false, found::put);
    return found.build();
  }

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f The input formula
   */
  @Override
  public Map<String, Formula> extractVariablesAndUFs(Formula f) {
    // Need LinkedHashMap because we can find duplicate keys with different values,
    // and ImmutableMap.Builder rejects them.
    Map<String, Formula> found = new LinkedHashMap<>();
    formulaCreator.extractVariablesAndUFs(f, true, found::put);
    return ImmutableMap.copyOf(found);
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula other, FormulaManager otherContext) {
    return parse(otherContext.dumpFormula(other).toString());
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    AbstractFormulaManager.checkVariableName(name);
    Formula t;
    if (formulaType.isBooleanType()) {
      t = booleanManager.makeVariable(name);
    } else if (formulaType.isIntegerType()) {
      assert integerManager != null;
      t = integerManager.makeVariable(name);
    } else if (formulaType.isRationalType()) {
      assert rationalManager != null;
      t = rationalManager.makeVariable(name);
    } else if (formulaType.isBitvectorType()) {
      assert bitvectorManager != null;
      t = bitvectorManager.makeVariable((BitvectorType) formulaType, name);
    } else if (formulaType.isFloatingPointType()) {
      assert floatingPointManager != null;
      t = floatingPointManager.makeVariable(name, (FloatingPointType) formulaType);
    } else if (formulaType.isArrayType()) {
      assert arrayManager != null;
      t = arrayManager.makeArray(name, (ArrayFormulaType<?, ?>) formulaType);
    } else {
      throw new IllegalArgumentException("Unknown formula type");
    }

    @SuppressWarnings("unchecked")
    T out = (T) t;
    return out;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    return formulaCreator.callFunction(declaration, args);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, Arrays.asList(args));
  }

  @Override
  public <T extends Formula> T substitute(
      final T pF, final Map<? extends Formula, ? extends Formula> pFromToMapping) {
    return transformRecursively(
        pF,
        new FormulaTransformationVisitor(this) {
          @Override
          public Formula visitFreeVariable(Formula f, String name) {
            return replace(f);
          }

          @Override
          public Formula visitFunction(
              Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
            Formula out = pFromToMapping.get(f);
            if (out == null) {
              return makeApplication(functionDeclaration, newArgs);
            } else {
              return out;
            }
          }

          private Formula replace(Formula f) {
            Formula out = pFromToMapping.get(f);
            if (out == null) {
              return f;
            } else {
              return out;
            }
          }
        });
  }

  /**
   * Check whether the given String can be used as symbol/name for variables or undefined functions.
   * We disallow some keywords from SMTLib2 and other basic operators to be used as symbols.
   *
   * <p>This method must be kept in sync with {@link #checkVariableName}.
   */
  @Override
  public boolean isValidName(String pVar) {
    if (pVar.isEmpty()) {
      return false;
    }
    if (BASIC_OPERATORS.contains(pVar)) {
      return false;
    }
    if (SMTLIB2_KEYWORDS.contains(pVar)) {
      return false;
    }
    if (DISALLOWED_CHARACTERS.matchesAnyOf(pVar)) {
      return false;
    }
    return true;
  }

  /**
   * This method is similar to {@link #isValidName} and throws an exception for invalid symbol
   * names. While {@link #isValidName} can be used from users, this method should be used internally
   * to validate user-given symbol names.
   *
   * <p>This method must be kept in sync with {@link #isValidName}.
   */
  static void checkVariableName(final String variableName) {
    final String help = "Use FormulaManager#isValidName to check your identifier before using it.";
    Preconditions.checkArgument(
        !variableName.isEmpty(), "Identifier for variable should not be empty.");
    Preconditions.checkArgument(
        !AbstractFormulaManager.BASIC_OPERATORS.contains(variableName),
        "Identifier '%s' should not be a simple operator. %s",
        variableName,
        help);
    Preconditions.checkArgument(
        !AbstractFormulaManager.SMTLIB2_KEYWORDS.contains(variableName),
        "Identifier '%s' should not be a keyword of SMT-LIB2. ",
        variableName,
        help);
    Preconditions.checkArgument(
        AbstractFormulaManager.DISALLOWED_CHARACTERS.matchesNoneOf(variableName),
        "Identifier '%s' should contain an escape character of SMT-LIB2. ",
        variableName,
        help);
  }
}
