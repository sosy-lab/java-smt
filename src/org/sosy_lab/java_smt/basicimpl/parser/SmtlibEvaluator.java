/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.parser;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;

public class SmtlibEvaluator {
  private final FormulaManager mgr;

  private final Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> globalDefs;
  private final List<BooleanFormula> asserted;

  private static int counter = 0;

  private SmtlibEvaluator(
      FormulaManager pManager,
      Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pGlobalDefs,
      List<BooleanFormula> pAsserted) {
    mgr = pManager;
    globalDefs = pGlobalDefs;
    asserted = pAsserted;
  }

  public static SmtlibEvaluator init(SolverContextFactory.Solvers pSolver) {
    throw new UnsupportedOperationException();
  }

  public static SmtlibEvaluator link(FormulaManager pManager) {
    return new SmtlibEvaluator(
        pManager, new Predefined(pManager).addTheorySymbols(), ImmutableList.of());
  }

  public SmtlibEvaluator apply(ParseTree pSmtlib) {
    return commandVisitor.visit(pSmtlib);
  }

  public List<BooleanFormula> getAssertions() {
    return asserted;
  }

  public static String genSymbol() {
    return String.format(".%s", counter++);
  }

  private static BigInteger getIntegerValue(SmtlibParser.IntegerContext ctx) {
    return new BigInteger(ctx.getText());
  }

  private static String getSymbolValue(SmtlibParser.SymbolContext ctx) {
    var str = ctx.getText();
    return str.charAt(0) == '|' ? str.substring(1, str.length() - 1) : str;
  }

  static class SortEvaluator extends SmtlibBaseVisitor<FormulaType<?>> {
    @Override
    public FormulaType<?> visitSortBool(SmtlibParser.SortBoolContext ctx) {
      return FormulaType.BooleanType;
    }

    @Override
    public FormulaType<?> visitSortInt(SmtlibParser.SortIntContext ctx) {
      return FormulaType.IntegerType;
    }

    @Override
    public FormulaType<?> visitSortReal(SmtlibParser.SortRealContext ctx) {
      return FormulaType.RationalType;
    }

    @Override
    public FormulaType<?> visitSortBitvec(SmtlibParser.SortBitvecContext ctx) {
      return FormulaType.getBitvectorTypeWithSize(getIntegerValue(ctx.integer()).intValueExact());
    }

    @Override
    public FormulaType<?> visitSortFloat(SmtlibParser.SortFloatContext ctx) {
      if (ctx.integer().isEmpty()) {
        switch (ctx.getText()) {
          case "Float16":
            return FormulaType.getFloatingPointType(5, 10);
          case "Float32":
            return FormulaType.getFloatingPointType(8, 23);
          case "Float64":
            return FormulaType.getFloatingPointType(11, 52);
          case "Float128":
            return FormulaType.getFloatingPointType(15, 112);
          default:
            throw new IllegalArgumentException(
                String.format("Unknown floating-point type: %s", ctx.getText()));
        }
      } else {
        return FormulaType.getFloatingPointType(
            getIntegerValue(ctx.integer(0)).intValueExact(),
            getIntegerValue(ctx.integer(1)).intValueExact());
      }
    }

    @Override
    public FormulaType<?> visitSortArray(SmtlibParser.SortArrayContext ctx) {
      return FormulaType.getArrayType(visit(ctx.sort(0)), visit(ctx.sort(1)));
    }
  }

  private SortEvaluator sortEvaluator = new SortEvaluator();

  class ConstEvalator extends SmtlibBaseVisitor<Formula> {
    @Override
    public Formula visitBoolean(SmtlibParser.BooleanContext ctx) {
      return mgr.getBooleanFormulaManager().makeBoolean(Boolean.parseBoolean(ctx.getText()));
    }

    @Override
    public Formula visitBitvec(SmtlibParser.BitvecContext ctx) {
      var str = ctx.getText().substring(2);
      if (ctx.getText().startsWith("#b")) {
        return mgr.getBitvectorFormulaManager().makeBitvector(str.length(), new BigInteger(str, 2));
      } else {
        return mgr.getBitvectorFormulaManager()
            .makeBitvector(str.length() * 4, new BigInteger(str, 16));
      }
    }

    @Override
    public Formula visitFloat(SmtlibParser.FloatContext ctx) {
      var b0 = ctx.bitvec(0).getText().substring(2);
      var b1 = ctx.bitvec(1).getText().substring(2);
      var b2 = ctx.bitvec(2).getText().substring(2);
      Preconditions.checkArgument(b0.length() == 1);
      return mgr.getFloatingPointFormulaManager()
          .makeNumber(FloatingPointNumber.of(b0 + b1 + b2, b1.length(), b2.length()));
    }

    @Override
    public Formula visitInteger(SmtlibParser.IntegerContext ctx) {
      return mgr.getIntegerFormulaManager().makeNumber(getIntegerValue(ctx));
    }

    @Override
    public Formula visitReal(SmtlibParser.RealContext ctx) {
      return mgr.getRationalFormulaManager().makeNumber(new BigDecimal(ctx.getText()));
    }
  }

  private ConstEvalator constEvalator = new ConstEvalator();

  class ExprEvaluator extends SmtlibBaseVisitor<Formula> {
    private final Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> context;

    class FunctionEvaluator extends SmtlibBaseVisitor<Function<List<Formula>, Formula>> {
      @Override
      public Function<List<Formula>, Formula> visitVar(SmtlibParser.VarContext ctx) {
        return lookup(getSymbolValue(ctx.symbol())).apply(ImmutableList.of());
      }

      @Override
      public Function<List<Formula>, Formula> visitIndexed(SmtlibParser.IndexedContext ctx) {
        return lookup(getSymbolValue(ctx.symbol()))
            .apply(
                FluentIterable.from(ctx.integer())
                    .transform(idx -> getIntegerValue(idx).intValueExact())
                    .toList());
      }

      @SuppressWarnings("unchecked")
      @Override
      public Function<List<Formula>, Formula> visitAs(SmtlibParser.AsContext ctx) {
        Preconditions.checkArgument(getSymbolValue(ctx.symbol()).equals("const"));
        var sort = sortEvaluator.visit(ctx.sort());
        Preconditions.checkArgument(sort.isArrayType());
        @SuppressWarnings("rawtypes")
        var arraySort = (FormulaType.ArrayFormulaType) sort;
        return value -> mgr.getArrayFormulaManager().makeArray(arraySort, value.get(0));
      }
    }

    private FunctionEvaluator functionEvaluator = new FunctionEvaluator();

    public ExprEvaluator(
        Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pContext) {
      context = pContext;
    }

    private Function<List<Integer>, Function<List<Formula>, Formula>> lookup(String symbol) {
      Preconditions.checkArgument(
          context.containsKey(symbol),
          "Symbol `%s` is not defined. Context has %s",
          symbol,
          context.isEmpty() ? "no symbols" : "symbols " + Joiner.on(", ").join(context.keySet()));
      return context.get(symbol);
    }

    @Override
    public Formula visitConst(SmtlibParser.ConstContext ctx) {
      return constEvalator.visit(ctx.children.get(0));
    }

    @Override
    public Formula visitVar(SmtlibParser.VarContext ctx) {
      return functionEvaluator.visit(ctx).apply(ImmutableList.of());
    }

    @Override
    public Formula visitIndexed(SmtlibParser.IndexedContext ctx) {
      return functionEvaluator.visit(ctx).apply(ImmutableList.of());
    }

    @Override
    public Formula visitAnnotated(SmtlibParser.AnnotatedContext ctx) {
      return visit(ctx.expr());
    }

    @Override
    public Formula visitLet(SmtlibParser.LetContext ctx) {
      Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> local =
          ImmutableMap.of();
      for (var binding : ctx.binding()) {
        var sym = getSymbolValue(binding.symbol());
        Preconditions.checkArgument(
            !local.containsKey(sym), "Let block contains more than one definition for %s", sym);
        var term = visit(binding.expr());
        local = addConstant(local, sym, term);
      }
      ImmutableMap.Builder<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
          builder = ImmutableMap.builder();
      var updated = builder.putAll(context).putAll(local).build();
      return new ExprEvaluator(updated).visit(ctx.expr());
    }

    @Override
    public Formula visitQuantified(SmtlibParser.QuantifiedContext ctx) {
      var variables = new ArrayList<Formula>();
      var updated = context;
      for (var sortedVar : ctx.sortedVar()) {
        var name = getSymbolValue(sortedVar.symbol());
        var sort = sortEvaluator.visit(sortedVar.sort());
        var term = mgr.makeVariable(sort, genSymbol());
        updated = addConstant(updated, name, term);
        variables.add(term);
      }
      var evaluated = new ExprEvaluator(updated).visit(ctx.expr());
      Preconditions.checkArgument(evaluated instanceof BooleanFormula);
      var acc = (BooleanFormula) evaluated;
      for (var bound : Lists.reverse(variables)) {
        acc =
            mgr.getQuantifiedFormulaManager()
                .mkQuantifier(
                    ctx.quantifier().getRuleIndex() == 0
                        ? QuantifiedFormulaManager.Quantifier.FORALL
                        : QuantifiedFormulaManager.Quantifier.EXISTS,
                    ImmutableList.of(bound),
                    acc);
      }
      return acc;
    }

    @Override
    public Formula visitApp(SmtlibParser.AppContext ctx) {
      var f = functionEvaluator.visit(ctx.expr(0));
      ImmutableList.Builder<Formula> builder = ImmutableList.builder();
      for (int i = 1; i < ctx.expr().size(); i++) {
        builder.add(visit(ctx.expr(i)));
      }
      return f.apply(builder.build());
    }
  }

  private static Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> addFunction(
      Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> context,
      String name,
      Function<List<Formula>, Formula> function) {
    ImmutableMap.Builder<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
        builder = ImmutableMap.builder();
    return builder
        .putAll(context)
        .put(
            name,
            idx -> {
              Preconditions.checkArgument(idx.isEmpty());
              return function;
            })
        .buildKeepingLast();
  }

  private static Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> addConstant(
      Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> context,
      String name,
      Formula value) {
    return addFunction(
        context,
        name,
        p -> {
          Preconditions.checkArgument(p.isEmpty());
          return value;
        });
  }

  class CommandVisitor extends SmtlibBaseVisitor<SmtlibEvaluator> {
    @Override
    public SmtlibEvaluator visitSetInfo(SmtlibParser.SetInfoContext ctx) {
      // Skip info command
      return SmtlibEvaluator.this;
    }

    @Override
    public SmtlibEvaluator visitSetOption(SmtlibParser.SetOptionContext ctx) {
      throw new IllegalArgumentException("Options are not supported");
    }

    @Override
    public SmtlibEvaluator visitSetLogic(SmtlibParser.SetLogicContext ctx) {
      var logic = ctx.symbol().getText();
      Preconditions.checkArgument(logic.equals("ALL"), "Logic must be set to ALL");
      return SmtlibEvaluator.this;
    }

    @Override
    public SmtlibEvaluator visitDeclare(SmtlibParser.DeclareContext ctx) {
      var name = getSymbolValue(ctx.symbol());
      var sorts = FluentIterable.from(ctx.sort()).transform(p -> sortEvaluator.visit(p)).toList();
      var left = sorts.subList(0, sorts.size() - 1);
      var right = sorts.get(sorts.size() - 1);
      if (sorts.size() == 1) {
        var term = mgr.makeVariable(right, name);
        return new SmtlibEvaluator(mgr, addConstant(globalDefs, name, term), asserted);
      } else {
        var uf = mgr.getUFManager().declareUF(name, right, left.toArray(new FormulaType<?>[0]));
        return new SmtlibEvaluator(
            mgr, addFunction(globalDefs, name, p -> mgr.makeApplication(uf, p)), asserted);
      }
    }

    @Override
    public SmtlibEvaluator visitDefine(SmtlibParser.DefineContext ctx) {
      var name = getSymbolValue(ctx.symbol());
      var sort = sortEvaluator.visit(ctx.sort());
      var parameters = ctx.sortedVar();
      if (parameters == null || parameters.isEmpty()) {
        var term = new ExprEvaluator(globalDefs).visit(ctx.expr());
        Preconditions.checkArgument(mgr.getFormulaType(term).equals(sort));
        return new SmtlibEvaluator(mgr, addConstant(globalDefs, name, term), asserted);
      } else {
        var capture = globalDefs;
        // TODO Evaluate once during creation to catch any errors right away
        return new SmtlibEvaluator(
            mgr,
            addFunction(
                globalDefs,
                name,
                p -> {
                  Preconditions.checkArgument(p.size() == parameters.size());
                  var updated = capture;
                  for (int i = 0; i < p.size(); i++) {
                    var nameArg = getSymbolValue(parameters.get(i).symbol());
                    var sortArg = sortEvaluator.visit(parameters.get(i).sort());
                    var value = p.get(i);
                    // FIXME Probably too strong for bv/fp sorts?
                    Preconditions.checkArgument(mgr.getFormulaType(value).equals(sortArg));
                    updated = addConstant(updated, nameArg, value);
                  }
                  return new ExprEvaluator(updated).visit(ctx.expr());
                }),
            asserted);
      }
    }

    @Override
    public SmtlibEvaluator visitAssert(SmtlibParser.AssertContext ctx) {
      var term = (BooleanFormula) new ExprEvaluator(globalDefs).visit(ctx.expr());
      return new SmtlibEvaluator(
          mgr, globalDefs, FluentIterable.concat(asserted, ImmutableList.of(term)).toList());
    }

    @Override
    public SmtlibEvaluator visitSmtlib(SmtlibParser.SmtlibContext ctx) {
      var eval = SmtlibEvaluator.this;
      for (var cmd : ctx.command()) {
        eval = eval.apply(cmd);
      }
      return eval;
    }
  }

  private final CommandVisitor commandVisitor = new CommandVisitor();
}
