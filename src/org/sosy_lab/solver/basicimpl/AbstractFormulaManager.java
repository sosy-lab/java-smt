/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.api.ArrayFormulaManager;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Declaration;
import org.sosy_lab.solver.api.DeclarationKind;
import org.sosy_lab.solver.api.FloatingPointFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.IntegerFormulaManager;
import org.sosy_lab.solver.api.RationalFormulaManager;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;
import org.sosy_lab.solver.visitors.DefaultFormulaVisitor;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;

/**
 * Simplifies building a solver from the specific theories.
 * @param <TFormulaInfo> The solver specific type.
 */
public abstract class AbstractFormulaManager<TFormulaInfo, TType, TEnv> implements FormulaManager {

  private final @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv> arrayManager;

  private final AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv> booleanManager;

  private final @Nullable IntegerFormulaManager integerManager;

  private final @Nullable RationalFormulaManager rationalManager;

  private final @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv>
      bitvectorManager;

  private final @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv>
      floatingPointManager;

  private final AbstractFunctionFormulaManager<TFormulaInfo, ?, TType, TEnv> functionManager;

  private final AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv> unsafeManager;

  private final @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv>
      quantifiedManager;

  private final FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator;

  /**
   * Builds a solver from the given theory implementations
   * @param unsafeManager the unsafe manager
   * @param functionManager the function theory
   * @param booleanManager the boolean theory
   * @param pIntegerManager the integer theory
   * @param pRationalManager the rational theory
   * @param bitvectorManager the bitvector theory
   */
  @SuppressWarnings("checkstyle:parameternumber")
  protected AbstractFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv> pFormulaCreator,
      AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv> unsafeManager,
      AbstractFunctionFormulaManager<TFormulaInfo, ?, TType, TEnv> functionManager,
      AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv> booleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv> bitvectorManager,
      @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv> floatingPointManager,
      @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv> quantifiedManager,
      @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv> arrayManager) {

    this.arrayManager = arrayManager;
    this.quantifiedManager = quantifiedManager;
    this.functionManager = checkNotNull(functionManager, "function manager needed");
    this.booleanManager = checkNotNull(booleanManager, "boolean manager needed");
    this.integerManager = pIntegerManager;
    this.rationalManager = pRationalManager;
    this.bitvectorManager = bitvectorManager;
    this.floatingPointManager = floatingPointManager;
    this.unsafeManager = checkNotNull(unsafeManager, "unsafe manager needed");
    this.formulaCreator = pFormulaCreator;

    if (booleanManager.getFormulaCreator() != formulaCreator
        || unsafeManager.getFormulaCreator() != formulaCreator
        || functionManager.getFormulaCreator() != formulaCreator
        || (bitvectorManager != null && bitvectorManager.getFormulaCreator() != formulaCreator)
        || (floatingPointManager != null
            && floatingPointManager.getFormulaCreator() != formulaCreator)) {
      throw new IllegalArgumentException("The creator instances must match across the managers!");
    }
  }

  public final FormulaCreator<TFormulaInfo, TType, TEnv> getFormulaCreator() {
    return formulaCreator;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    if (integerManager == null) {
      // TODO fallback to rationalManager?
      throw new UnsupportedOperationException();
    }
    return integerManager;
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    if (rationalManager == null) {
      // TODO fallback to integerManager?
      throw new UnsupportedOperationException();
    }
    return rationalManager;
  }

  @Override
  public AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv> getBooleanFormulaManager() {
    return booleanManager;
  }

  @Override
  public AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv> getBitvectorFormulaManager() {
    if (bitvectorManager == null) {
      throw new UnsupportedOperationException();
    }
    return bitvectorManager;
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    if (floatingPointManager == null) {
      throw new UnsupportedOperationException();
    }
    return floatingPointManager;
  }

  @Override
  public AbstractFunctionFormulaManager<TFormulaInfo, ?, TType, TEnv> getFunctionFormulaManager() {
    return functionManager;
  }

  @Override
  public AbstractUnsafeFormulaManager<TFormulaInfo, TType, TEnv> getUnsafeFormulaManager() {
    return unsafeManager;
  }

  @Override
  public AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv> getQuantifiedFormulaManager() {
    if (quantifiedManager == null) {
      throw new UnsupportedOperationException();
    }
    return quantifiedManager;
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    if (arrayManager == null) {
      throw new UnsupportedOperationException();
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
  public BooleanFormula applyTactic(BooleanFormula f, Tactic tactic) {
    return formulaCreator.encapsulateBoolean(applyTacticImpl(extractInfo(f), tactic));
  }

  protected TFormulaInfo applyTacticImpl(TFormulaInfo f, Tactic tactic) {
    return extractInfo(tactic.applyDefault(this, formulaCreator.encapsulateBoolean(f)));
  }

  @Override
  public <T extends Formula> T simplify(T f) {
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), simplify(extractInfo(f)));
  }

  protected TFormulaInfo simplify(TFormulaInfo f) {
    return f;
  }

  @Override
  public void visitRecursively(FormulaVisitor<TraversalProcess> pFormulaVisitor, Formula pF) {
    RecursiveFormulaVisitor recVisitor = new RecursiveFormulaVisitor(pFormulaVisitor);
    recVisitor.addToQueue(pF);
    while (!recVisitor.isQueueEmpty()) {
      TraversalProcess process = checkNotNull(visit(recVisitor, recVisitor.pop()));
      if (process == TraversalProcess.ABORT) {
        return;
      }
    }
  }

  /**
   * Extract names of all free variables in a formula.
   *
   * @param f   The input formula
   * @return    Set of variable names.
   */
  public Set<String> extractVariableNames(Formula f) {
    return myExtractSubformulas(f, false).keySet();
  }

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   * @return    Set of variable names.
   */
  public Set<String> extractFunctionNames(Formula f) {
    return myExtractSubformulas(f, true).keySet();
  }

  /**
   * Extract all free variables from the formula, optionally including UFs.
   */
  protected Map<String, Formula> myExtractSubformulas(
      final Formula pFormula, final boolean extractUF) {

    final Map<String, Formula> found = new HashMap<>();
    visitRecursively(
        new DefaultFormulaVisitor<TraversalProcess>() {

          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFunction(
              Formula f,
              List<Formula> args,
              Declaration functionDeclaration,
              Function<List<Formula>, Formula> constructor) {

            if (functionDeclaration.getKind() == DeclarationKind.UF && extractUF) {
              found.put(functionDeclaration.getName(), f);
            }
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula f, String name) {
            found.put(name, f);
            return TraversalProcess.CONTINUE;
          }
        },
        pFormula);
    return found;
  }
}
