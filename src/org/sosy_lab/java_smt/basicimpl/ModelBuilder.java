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

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
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
    mgr = pFormulaManager;
  }

  private Map<List<Formula>, Formula> collectArrayIndices(List<Formula> pIndices, Formula pValue) {
    if (pValue instanceof ArrayFormula) {
      return mgr.visit(
          pValue,
          new DefaultFormulaVisitor<>() {
            @Override
            protected Map<List<Formula>, Formula> visitDefault(Formula f) {
              throw new IllegalArgumentException();
            }

            @Override
            public Map<List<Formula>, Formula> visitFunction(
                Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
              if (functionDeclaration.getKind().equals(FunctionDeclarationKind.CONST)) {
                return ImmutableMap.of();
              } else if (functionDeclaration.getKind().equals(FunctionDeclarationKind.STORE)) {
                var nextIndex =
                    collectArrayIndices(
                        FluentIterable.concat(pIndices, ImmutableList.of(args.get(1))).toList(),
                        args.get(2));
                var nextMatch = collectArrayIndices(pIndices, args.get(0));

                ImmutableMap.Builder<List<Formula>, Formula> builder = ImmutableMap.builder();
                builder.putAll(nextIndex);
                builder.putAll(nextMatch);
                return builder.build();
              } else {
                throw new IllegalArgumentException();
              }
            }
          });
    } else {
      return ImmutableMap.of(pIndices, pValue);
    }
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

  private Object getConstantValue(Formula pConstant) {
    return mgr.visit(
        pConstant,
        new DefaultFormulaVisitor<>() {
          @Override
          protected Object visitDefault(Formula f) {
            throw new IllegalArgumentException();
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
              throw new IllegalArgumentException();
            }
          }
        });
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

  /** Convert a "Store" term into a list of assignments. */
  public ImmutableList<ValueAssignment> buildArrayAssignments(
      ArrayFormula<?, ?> pVariable, Formula pValue) {
    var values = collectArrayIndices(ImmutableList.of(), pValue);
    return FluentIterable.from(values.entrySet())
        .transform(
            entry -> {
              var idx = entry.getKey();
              var left = buildSelectTerm(pVariable, idx);
              var right = entry.getValue();

              return new ValueAssignment(
                  left,
                  right,
                  mgr.equal(left, right),
                  getVariableName(pVariable),
                  getConstantValue(right),
                  FluentIterable.from(idx).transform(this::getConstantValue).toList());
            })
        .toList();
  }

  @SuppressWarnings("unused")
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
                    functionDeclaration,
                    FluentIterable.from(newArgs).transform(pEval::apply).toList()),
                pEval.apply(f));
          }
        }
        return f;
      }

      Map<Formula, Formula> getUfTerms() {
        return ufTerms;
      }
    }
    var ufTerms = new UFVisitor();
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
   * @param eval function to evaluate terms to values in the current model
   */
  public ImmutableList<ValueAssignment> buildUfAssignments(
      Formula pAssertions, Function<Formula, Formula> eval) {
    var ufTerms = collectUFTerms(pAssertions, eval);
    return FluentIterable.from(ufTerms.entrySet())
        .transform(
            entry -> {
              var left = entry.getKey();
              var right = entry.getValue();

              return new ValueAssignment(
                  left,
                  right,
                  mgr.equal(left, right),
                  getUfName(left),
                  getConstantValue(right),
                  FluentIterable.from(getUfArgs(left)).transform(this::getConstantValue).toList());
            })
        .toList();
  }

  /** Create an assignment for a normal variable. */
  public ValueAssignment buildVariableAssignment(Formula pVariable, Formula pValue) {
    return new ValueAssignment(
        pVariable,
        pValue,
        mgr.equal(pVariable, pValue),
        getVariableName(pVariable),
        getConstantValue(pValue),
        ImmutableList.of());
  }
}
