/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Table;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

public class ModelBuilder {
  private final FormulaManager mgr;

  public ModelBuilder(FormulaManager pFormulaManager) {
    mgr = checkNotNull(pFormulaManager);
  }

  private String getVariableName(Formula pVariable) {
    return mgr.visit(
        pVariable,
        new DefaultFormulaVisitor<>() {
          @Override
          protected String visitDefault(Formula f) {
            throw new IllegalArgumentException();
          }

          @Override
          public String visitFreeVariable(Formula f, String name) {
            return name;
          }
        });
  }

  private @Nullable Object getConstantValue(Formula pConstant) {
    return mgr.visit(
        pConstant,
        new DefaultFormulaVisitor<>() {
          @Override
          protected Object visitDefault(Formula f) {
            return null;
          }

          @Override
          public Object visitConstant(Formula f, Object value) {
            return value;
          }

          @Override
          public Object visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            if (functionDeclaration.getKind().equals(FunctionDeclarationKind.CONST)
                || functionDeclaration.getKind().equals(FunctionDeclarationKind.STORE)) {
              return f;
            } else {
              return null;
            }
          }
        });
  }

  /** Create an assignment for a normal variable. */
  public List<ValueAssignment> buildVariableAssignment(Formula pVariable, Formula pValue) {
    var evaluated = getConstantValue(pValue);
    if (evaluated != null) {
      return ImmutableList.of(
          new ValueAssignment(
              pVariable,
              pValue,
              mgr.equal(pVariable, pValue),
              getVariableName(pVariable),
              evaluated,
              ImmutableList.of()));
    } else {
      return ImmutableList.of();
    }
  }

  private Map<Formula, Formula> collectUFTerms(
      Formula pAssertions, Function<Formula, Formula> pEval) {
    class UFVisitor extends DefaultFormulaVisitor<Optional<Formula>> {
      private final Map<Formula, Formula> ufTerms = new HashMap<>();
      private List<Formula> scope = new ArrayList<>();

      @Override
      protected Optional<Formula> visitDefault(Formula f) {
        var value = pEval.apply(f);
        return !scope.contains(f) && value != null ? Optional.of(value) : Optional.empty();
      }

      @Override
      public Optional<Formula> visitFunction(
          Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
        ImmutableList.Builder<Formula> argBuilder = ImmutableList.builder();
        for (var arg : args) {
          var evaluated = mgr.visit(arg, this);
          if (evaluated.isPresent()) {
            argBuilder.add(evaluated.orElseThrow());
          }
        }
        var newArgs = argBuilder.build();
        var value = pEval.apply(f);
        if (newArgs.size() == args.size() && value != null) {
          if (functionDeclaration.getKind().equals(FunctionDeclarationKind.UF)) {
            ufTerms.put(mgr.makeApplication(functionDeclaration, newArgs), value);
          }
          return Optional.of(value);
        } else {
          return Optional.empty();
        }
      }

      @Override
      public Optional<Formula> visitQuantifier(
          BooleanFormula f,
          Quantifier quantifier,
          List<Formula> boundVariables,
          BooleanFormula body) {
        int last = scope.size();
        scope.addAll(boundVariables);
        var r = mgr.visit(body, this);
        scope = scope.subList(0, last);
        return r;
      }

      Map<Formula, Formula> getUfTerms() {
        return ufTerms;
      }
    }
    checkNotNull(pEval);
    var ufTerms = new UFVisitor();
    mgr.visit(pAssertions, ufTerms);
    return ufTerms.getUfTerms();
  }

  private String getUfName(Formula pApp) {
    return mgr.visit(
        pApp,
        new DefaultFormulaVisitor<>() {
          @Override
          protected String visitDefault(Formula f) {
            throw new IllegalArgumentException();
          }

          @Override
          public String visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            if (functionDeclaration.getKind().equals(FunctionDeclarationKind.UF)) {
              return functionDeclaration.getName();
            } else {
              throw new IllegalArgumentException();
            }
          }
        });
  }

  private List<Formula> getUfArgs(Formula pApp) {
    return mgr.visit(
        pApp,
        new DefaultFormulaVisitor<>() {
          @Override
          protected List<Formula> visitDefault(Formula f) {
            throw new IllegalArgumentException();
          }

          @Override
          public List<Formula> visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            if (functionDeclaration.getKind().equals(FunctionDeclarationKind.UF)) {
              return args;
            } else {
              throw new IllegalArgumentException();
            }
          }
        });
  }

  /**
   * Build assignments for all UFs in the asserted formulas.
   *
   * @param pAssertions conjunction of all assertions on the stack
   * @param eval function to evaluate terms to values in the current model
   */
  public ImmutableList<ValueAssignment> buildUfAssignments(
      Formula pAssertions, Function<Formula, Formula> eval) {
    var ufTerms = collectUFTerms(pAssertions, eval);

    ImmutableList.Builder<ValueAssignment> assignmentBuilder = ImmutableList.builder();
    for (var entry : ufTerms.entrySet()) {
      var left = entry.getKey();
      var right = entry.getValue();

      ImmutableList.Builder<Object> argBuilder = ImmutableList.builder();
      var ufArgs = getUfArgs(left);
      for (var arg : ufArgs) {
        var value = getConstantValue(arg);
        if (value != null) {
          argBuilder.add(value);
        }
      }
      var value = getConstantValue(right);
      if (ufArgs.size() == argBuilder.build().size() && value != null) {
        assignmentBuilder.add(
            new ValueAssignment(
                left, right, mgr.equal(left, right), getUfName(left), value, argBuilder.build()));
      }
    }
    return assignmentBuilder.build();
  }

  public Map<Formula, Map<Formula, Formula>> collectArrayValues(
      Formula pAssertions, Function<Formula, Formula> pEval) {
    class ArrayVisitor extends DefaultFormulaVisitor<Optional<Formula>> {
      private final Table<Formula, Formula, Formula> arrayTerms = HashBasedTable.create();
      private List<Formula> scope = new ArrayList<>();

      @Override
      protected Optional<Formula> visitDefault(Formula f) {
        if (scope.contains(f)) {
          return Optional.empty();
        } else {
          var value = pEval.apply(f);
          if (!f.equals(value) && value != null) {
            return mgr.visit(value, this);
          } else {
            return Optional.of(f);
          }
        }
      }

      @Override
      public Optional<Formula> visitFunction(
          Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
        ImmutableList.Builder<Formula> argBuilder = ImmutableList.builder();
        for (var arg : args) {
          var evaluated = mgr.visit(arg, this);
          if (evaluated.isPresent()) {
            argBuilder.add(evaluated.orElseThrow());
          }
        }
        var newArgs = argBuilder.build();
        var value = pEval.apply(f);
        if (newArgs.size() == args.size() && value != null) {
          if (functionDeclaration.getKind().equals(FunctionDeclarationKind.SELECT)) {
            arrayTerms.put(newArgs.get(0), newArgs.get(1), value);
          }
          if (functionDeclaration.getKind().equals(FunctionDeclarationKind.STORE)) {
            arrayTerms.put(value, newArgs.get(1), newArgs.get(2));
          }
          return Optional.of(value);
        } else {
          return Optional.empty();
        }
      }

      @Override
      public Optional<Formula> visitQuantifier(
          BooleanFormula f,
          Quantifier quantifier,
          List<Formula> boundVariables,
          BooleanFormula body) {
        int last = scope.size();
        scope.addAll(boundVariables);
        var r = mgr.visit(body, this);
        scope = scope.subList(0, last);
        return r;
      }

      Map<Formula, Map<Formula, Formula>> getArrayTerms() {
        return arrayTerms.rowMap();
      }
    }

    checkNotNull(pEval);

    var arrayTerms = new ArrayVisitor();
    mgr.visit(pAssertions, arrayTerms);
    return arrayTerms.getArrayTerms();
  }

  private Map<List<Formula>, Formula> buildArrayAssignments0(
      Map<Formula, Map<Formula, Formula>> pArrayIndices, List<Formula> indices, Formula pValue) {
    if (!mgr.getFormulaType(pValue).isArrayType()) {
      return ImmutableMap.of(indices, pValue);
    } else {
      ImmutableMap.Builder<List<Formula>, Formula> builder = ImmutableMap.builder();
      for (var entry : pArrayIndices.getOrDefault(pValue, ImmutableMap.of()).entrySet()) {
        builder.putAll(
            buildArrayAssignments0(
                pArrayIndices,
                FluentIterable.concat(
                        FluentIterable.from(indices), ImmutableList.of(entry.getKey()))
                    .toList(),
                entry.getValue()));
      }
      return builder.buildOrThrow();
    }
  }

  @SuppressWarnings({"unchecked", "rawtypes"})
  private Formula buildSelectTerm(Formula pArray, List<Formula> pIndices) {
    if (pIndices.isEmpty()) {
      return pArray;
    } else {
      return buildSelectTerm(
          mgr.getArrayFormulaManager().select((ArrayFormula) pArray, pIndices.get(0)),
          pIndices.subList(1, pIndices.size()));
    }
  }

  public ImmutableList<ValueAssignment> buildArrayAssignments(
      Map<Formula, Map<Formula, Formula>> pArrayIndices,
      ArrayFormula<?, ?> pVariable,
      Formula pValue) {
    checkNotNull(pArrayIndices);
    var values = buildArrayAssignments0(pArrayIndices, ImmutableList.of(), pValue);

    ImmutableList.Builder<ValueAssignment> assignmentBuilder = ImmutableList.builder();
    for (var entry : values.entrySet()) {
      var idx = entry.getKey();
      var left = buildSelectTerm(pVariable, idx);
      var right = entry.getValue();

      ImmutableList.Builder<Object> argBuilder = ImmutableList.builder();
      var ufArgs = idx;
      for (var arg : ufArgs) {
        var value = getConstantValue(arg);
        if (value != null) {
          argBuilder.add(value);
        }
      }
      var newArgs = argBuilder.build();
      var newValue = getConstantValue(right);
      if (ufArgs.size() == newArgs.size() && newValue != null) {
        assignmentBuilder.add(
            new ValueAssignment(
                left,
                right,
                mgr.equal(left, right),
                getVariableName(pVariable),
                newValue,
                newArgs));
      }
    }
    return assignmentBuilder.build();
  }
}
