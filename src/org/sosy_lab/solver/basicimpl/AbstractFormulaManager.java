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
import com.google.common.collect.Lists;

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.api.ArrayFormulaManager;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FloatingPointFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.api.IntegerFormulaManager;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.api.RationalFormulaManager;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;
import org.sosy_lab.solver.visitors.DefaultFormulaVisitor;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

  protected final AbstractIntrospectionFormulaManager<TFormulaInfo, TType, TEnv>
      introspectionManager;

  private final @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv>
      quantifiedManager;

  private final FormulaCreator<TFormulaInfo, TType, TEnv> formulaCreator;

  /**
   * Builds a solver from the given theory implementations
   */
  @SuppressWarnings("checkstyle:parameternumber")
  protected AbstractFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv> pFormulaCreator,
      AbstractIntrospectionFormulaManager<TFormulaInfo, TType, TEnv> introspectionManager,
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
    this.introspectionManager = checkNotNull(introspectionManager, "unsafe manager needed");
    this.formulaCreator = pFormulaCreator;

    if (booleanManager.getFormulaCreator() != formulaCreator
        || introspectionManager.getFormulaCreator() != formulaCreator
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
    introspectionManager.visitRecursively(pFormulaVisitor, pF);
  }

  /**
   * Extract names of all free variables in a formula.
   *
   * @param f   The input formula
   */
  public Map<String, Formula> extractVariableNames(Formula f) {
    return myExtractSubformulas(f, false);
  }

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   */
  public Map<String, Formula> extractFunctionNames(Formula f) {
    return myExtractSubformulas(f, true);
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
          public TraversalProcess visitFuncApp(
              Formula f,
              List<Formula> args,
              FuncDecl functionDeclaration,
              Function<List<Formula>, Formula> constructor) {

            if (functionDeclaration.getKind() == FuncDeclKind.UF && extractUF) {
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

  private <T extends Formula> T encapsulateWithTypeOf(T f, TFormulaInfo e) {
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), e);
  }

  @Override
  public <T extends Formula> List<T> splitNumeralEqualityIfPossible(final T pF) {
    return Lists.transform(
        splitNumeralEqualityIfPossible(extractInfo(pF)),
        new Function<TFormulaInfo, T>() {
          @Override
          public T apply(TFormulaInfo input) {
            return encapsulateWithTypeOf(pF, input);
          }
        });
  }

  protected abstract List<? extends TFormulaInfo> splitNumeralEqualityIfPossible(TFormulaInfo pF);

  /**
   * Default implementation for {@link #substitute(Formula, Map)}.
   */
  protected final <T1 extends Formula, T2 extends Formula> T1 substituteUsingMap(
      T1 pF, Map<T2, T2> pFromToMapping) {
    Map<TFormulaInfo, TFormulaInfo> mapping = new HashMap<>(pFromToMapping.size());
    for (Map.Entry<T2, T2> entry : pFromToMapping.entrySet()) {
      mapping.put(extractInfo(entry.getKey()), extractInfo(entry.getValue()));
    }

    TFormulaInfo result = substituteUsingMapImpl(extractInfo(pF), mapping, pF, pFromToMapping);
    FormulaType<T1> type = getFormulaCreator().getFormulaType(pF);
    return getFormulaCreator().encapsulate(type, result);
  }

  protected TFormulaInfo substituteUsingMapImpl(
      TFormulaInfo expr,
      Map<TFormulaInfo, TFormulaInfo> memoization,
      Formula f,
      final Map<? extends Formula, ? extends Formula> fromToMapping) {

    final Deque<Formula> toProcess = new ArrayDeque<>();
    final Map<Formula, Formula> pCache = new HashMap<>();

    // Add the formula to the work queue
    toProcess.push(f);

    FormulaVisitor<Void> process =
        new DefaultFormulaVisitor<Void>() {

          @Override
          protected Void visitDefault(Formula f) {
            Formula out = fromToMapping.get(f);
            if (out == null) {
              out = f;
            }
            pCache.put(f, out);
            return null;
          }

          @Override
          public Void visitBoundVariable(Formula f, int deBruijnIdx) {

            // Bound variables have to stay as-is.
            pCache.put(f, f);
            return null;
          }

          @Override
          public Void visitFuncApp(
              Formula f,
              List<Formula> args,
              FuncDecl decl,
              Function<List<Formula>, Formula> newApplicationConstructor) {
            Formula out = fromToMapping.get(f);
            if (out != null) {
              pCache.put(f, out);
              return null;
            }

            boolean allArgumentsTransformed = true;

            // Construct a new argument list for the function application.
            List<Formula> newArgs = new ArrayList<>(args.size());

            for (Formula c : args) {
              Formula newC = pCache.get(c);

              if (newC != null) {
                newArgs.add(newC);
              } else {
                toProcess.push(c);
                allArgumentsTransformed = false;
              }
            }

            // The Flag allArgumentsTransformed indicates whether all arguments
            // of the function were already processed.
            if (allArgumentsTransformed) {

              // Create an processed version of the
              // function application.
              toProcess.pop();
              out = newApplicationConstructor.apply(newArgs);
              pCache.put(f, out);
            }
            return null;
          }

          @Override
          public Void visitQuantifier(
              BooleanFormula f, Quantifier quantifier, List<Formula> args, BooleanFormula body) {
            BooleanFormula transformedBody = (BooleanFormula) pCache.get(body);

            if (transformedBody != null) {
              BooleanFormula newTt =
                  getQuantifiedFormulaManager().mkQuantifier(quantifier, args, transformedBody);
              pCache.put(f, newTt);

            } else {
              toProcess.push(body);
            }
            return null;
          }
        };

    // Process the work queue
    while (!toProcess.isEmpty()) {
      Formula tt = toProcess.peek();

      if (pCache.containsKey(tt)) {
        toProcess.pop();
        continue;
      }

      //noinspection ResultOfMethodCallIgnored
      visit(process, tt);
    }

    return formulaCreator.extractInfo(pCache.get(f));
  }

  /**
   * Default implementation for {@link #substitute(Formula, Map)} for solvers that provide
   * an internal substitute operation that takes two lists instead of a map.
   *
   * <p>If this is called, one needs to overwrite
   * {@link #substitute(Formula, Map)}.
   */
  protected final <T1 extends Formula, T2 extends Formula> T1 substituteUsingLists(
      T1 pF, Map<T2, T2> pFromToMapping) {
    List<TFormulaInfo> substituteFrom = new ArrayList<>(pFromToMapping.size());
    List<TFormulaInfo> substituteTo = new ArrayList<>(pFromToMapping.size());
    for (Map.Entry<T2, T2> entry : pFromToMapping.entrySet()) {
      substituteFrom.add(extractInfo(entry.getKey()));
      substituteTo.add(extractInfo(entry.getValue()));
    }

    TFormulaInfo result = substituteUsingListsImpl(extractInfo(pF), substituteFrom, substituteTo);
    FormulaType<T1> type = getFormulaCreator().getFormulaType(pF);
    return getFormulaCreator().encapsulate(type, result);
  }

  /**
   * Backend for {@link #substituteUsingLists(Formula, Map)}.
   * @param pF The formula to change.
   * @param substituteFrom The list of parts that should be replaced.
   * @param substituteTo The list of replacement parts, in same order.
   * @return The formula with th replacements applied.
   */
  protected TFormulaInfo substituteUsingListsImpl(
      TFormulaInfo pF, List<TFormulaInfo> substituteFrom, List<TFormulaInfo> substituteTo) {
    throw new UnsupportedOperationException();
  }
}
