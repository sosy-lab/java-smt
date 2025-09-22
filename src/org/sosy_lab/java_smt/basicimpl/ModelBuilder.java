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
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Table;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;

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
    class UFVisitor extends FormulaTransformationVisitor {
      private final Map<Formula, Formula> ufTerms = new HashMap<>();

      UFVisitor() {
        super(mgr);
      }

      @Override
      public Formula visitFunction(
          Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
        if (functionDeclaration.getKind().equals(FunctionDeclarationKind.UF)) {
          ImmutableList.Builder<Formula> builder = ImmutableList.builder();
          for (var arg : newArgs) {
            var value = pEval.apply(arg);
            if (value != null) {
              builder.add(value);
            }
          }
          var evaluated = builder.build();
          if (evaluated.size() == newArgs.size()) {
            ufTerms.put(
                mgr.makeApplication(
                    functionDeclaration, transformedImmutableListCopy(newArgs, pEval::apply)),
                pEval.apply(f));
          }
        }
        return f;
      }

      Map<Formula, Formula> getUfTerms() {
        return ufTerms;
      }
    }
    checkNotNull(pEval);
    var ufTerms = new UFVisitor();
    @SuppressWarnings("unused")
    var unused = mgr.transformRecursively(pAssertions, ufTerms);
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
      if (ufArgs.size() == argBuilder.build().size()) {
        assignmentBuilder.add(
            new ValueAssignment(
                left,
                right,
                mgr.equal(left, right),
                getUfName(left),
                getConstantValue(right),
                argBuilder.build()));
      }
    }

    return assignmentBuilder.build();
  }

  public Map<Formula, Map<Formula, Formula>> collectArrayValues(
      Formula pAssertions, Function<Formula, Formula> pEval) {
    class ArrayVisitor extends FormulaTransformationVisitor {
      private final Table<Formula, Formula, Formula> arrayTerms = HashBasedTable.create();

      ArrayVisitor() {
        super(mgr);
      }

      @Override
      public Formula visitFreeVariable(Formula f, String name) {
        var value = pEval.apply(f);
        if (!f.equals(value)) {
          @SuppressWarnings("unused")
          var unused = mgr.transformRecursively(value, this);
        }
        return f;
      }

      @Override
      public Formula visitFunction(
          Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
        if (functionDeclaration.getKind().equals(FunctionDeclarationKind.SELECT)) {
          ImmutableList.Builder<Formula> builder = ImmutableList.builder();
          for (var arg : newArgs) {
            var value = pEval.apply(arg);
            if (value != null) {
              builder.add(value);
            }
          }
          var evaluated = builder.build();
          if (evaluated.size() == newArgs.size()) {
            arrayTerms.put(evaluated.get(0), evaluated.get(1), pEval.apply(f));
          }
        }
        if (functionDeclaration.getKind().equals(FunctionDeclarationKind.STORE)) {
          ImmutableList.Builder<Formula> builder = ImmutableList.builder();
          for (var arg : newArgs) {
            var value = pEval.apply(arg);
            if (value != null) {
              builder.add(value);
            }
          }
          var evaluated = builder.build();
          if (evaluated.size() == newArgs.size()) {
            arrayTerms.put(pEval.apply(f), evaluated.get(1), evaluated.get(2));
          }
        }
        return f;
      }

      Map<Formula, Map<Formula, Formula>> getArrayTerms() {
        return arrayTerms.rowMap();
      }
    }
    checkNotNull(pEval);
    var arrayTerms = new ArrayVisitor();
    @SuppressWarnings("unused")
    var unused = mgr.transformRecursively(pAssertions, arrayTerms);
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
