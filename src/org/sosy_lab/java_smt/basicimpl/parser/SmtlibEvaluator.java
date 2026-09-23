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

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager.SolverResponse.CheckSatResponse.Status;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager;

public class SmtlibEvaluator {
  public enum ParsingMode {
    TERM,
    SCRIPT
  }

  private final ParsingMode mode;
  private final SolverContext solver;
  private final FormulaManager mgr;
  private final ProverEnvironment prover;
  private final boolean closed;

  private final Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> globalDefs;
  private final Set<String> localDefs;
  private final List<List<BooleanFormula>> asserted;
  private final Optional<List<BooleanFormula>> lastAssumptions;
  private final ImmutableList.Builder<FormulaManager.SolverResponse> responses;

  private static int counter = 0;

  private SmtlibEvaluator(
      ParsingMode pMode,
      SolverContext pSolver,
      ProverEnvironment pProver,
      boolean pClosed,
      Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pGlobalDefs,
      Set<String> pLocalDefs,
      List<List<BooleanFormula>> pAsserted,
      Optional<List<BooleanFormula>> pLastAssumptions,
      ImmutableList.Builder<FormulaManager.SolverResponse> pResponses) {
    mode = pMode;
    solver = pSolver;
    mgr = pSolver.getFormulaManager();
    prover = pProver;
    closed = pClosed;
    globalDefs = pGlobalDefs;
    localDefs = pLocalDefs;
    asserted = pAsserted;
    lastAssumptions = pLastAssumptions;
    responses = pResponses;
  }

  private static ProverEnvironment newProver(SolverContext pSolver) {
    var newProver =
        pSolver.newProverEnvironment(
            SolverContext.ProverOptions.GENERATE_MODELS,
            SolverContext.ProverOptions.GENERATE_UNSAT_CORE,
            SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    try {
      // Start with one level, so that we can pop all formulas that will be added
      newProver.push();
    } catch (InterruptedException e) {
      sneakyThrow(e);
    }
    return newProver;
  }

  @SuppressWarnings("resource")
  public static SmtlibEvaluator link(
      SolverContext pSolver, ParsingFormulaManager pManager, ParsingMode pMode) {
    return new SmtlibEvaluator(
        pMode,
        pSolver,
        newProver(pSolver),
        false,
        new Predefined(pManager)
            .addTheorySymbols()
            .addUserSymbols(pManager.getDefinedSymbols())
            .build(),
        ImmutableSet.of(),
        ImmutableList.of(ImmutableList.of()),
        Optional.empty(),
        ImmutableList.builder());
  }

  public SmtlibEvaluator apply(ParseTree pSmtlib) {
    return commandVisitor.visit(pSmtlib);
  }

  public List<BooleanFormula> getAssertions() {
    ImmutableList.Builder<BooleanFormula> builder = ImmutableList.builder();
    for (var level : asserted) {
      builder.addAll(level);
    }
    return builder.build();
  }

  public List<FormulaManager.SolverResponse> getResponses() {
    return responses.build();
  }

  @SuppressWarnings("unchecked")
  private static <E extends Throwable> void sneakyThrow(Throwable e) throws E {
    throw (E) e;
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
        return switch (ctx.getText()) {
          case "Float16" -> FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(5, 11);
          case "Float32" -> FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(8, 24);
          case "Float64" -> FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(11, 53);
          case "Float128" -> FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(15, 113);
          default ->
              throw new IllegalArgumentException(
                  String.format("Unknown floating-point type: %s", ctx.getText()));
        };
      } else {
        return FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(
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
      checkArgument(b0.length() == 1);
      return mgr.getFloatingPointFormulaManager()
          .makeNumber(
              FloatingPointNumber.of(
                  b0 + b1 + b2,
                  FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(
                      b1.length(), b2.length())));
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
        var symbol = getSymbolValue(ctx.symbol());
        if (symbol.matches("bv\\d+")) {
          // Special case: BV defines symbols (_ bvX m) to create bitvector literals. Here we
          // have to get the value of the bitvector straight from the symbol name
          checkArgument(ctx.integer().size() == 1);
          return p -> {
            checkArgument(p.isEmpty());
            return mgr.getBitvectorFormulaManager()
                .makeBitvector(
                    getIntegerValue(ctx.integer(0)).intValueExact(),
                    new BigInteger(symbol.substring(2)));
          };
        } else {
          return lookup(getSymbolValue(ctx.symbol()))
              .apply(
                  transformedImmutableListCopy(
                      ctx.integer(), idx -> getIntegerValue(idx).intValueExact()));
        }
      }

      @SuppressWarnings("unchecked")
      @Override
      public Function<List<Formula>, Formula> visitAs(SmtlibParser.AsContext ctx) {
        checkArgument(getSymbolValue(ctx.symbol()).equals("const"));
        var sort = sortEvaluator.visit(ctx.sort());
        checkArgument(sort.isArrayType());
        @SuppressWarnings("rawtypes")
        var arraySort = (FormulaType.ArrayFormulaType) sort;
        return value -> mgr.getArrayFormulaManager().makeArray(arraySort, value.get(0));
      }
    }

    private FunctionEvaluator functionEvaluator = new FunctionEvaluator();

    ExprEvaluator(Map<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pContext) {
      context = pContext;
    }

    private Function<List<Integer>, Function<List<Formula>, Formula>> lookup(String symbol) {
      checkArgument(
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
        checkArgument(
            !local.containsKey(sym), "Let block contains more than one definition for %s", sym);
        var term = visit(binding.expr());
        local = addConstant(local, sym, term);
      }
      ImmutableMap.Builder<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
          builder = ImmutableMap.builder();
      var updated = builder.putAll(context).putAll(local).buildOrThrow();
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
      checkArgument(evaluated instanceof BooleanFormula);
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
              checkArgument(idx.isEmpty());
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
          checkArgument(p.isEmpty());
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
      checkArgument(logic.equals("ALL"), "Logic must be set to ALL");
      return SmtlibEvaluator.this;
    }

    @Override
    public SmtlibEvaluator visitDeclare(SmtlibParser.DeclareContext ctx) {
      var name = getSymbolValue(ctx.symbol());
      checkArgument(!localDefs.contains(name), "Symbol %s already exists", name);
      var sorts = transformedImmutableListCopy(ctx.sort(), p -> sortEvaluator.visit(p));
      var left = sorts.subList(0, sorts.size() - 1);
      var right = sorts.get(sorts.size() - 1);
      if (sorts.size() == 1) {
        var term = mgr.makeVariable(right, name);
        return new SmtlibEvaluator(
            mode,
            solver,
            prover,
            closed,
            addConstant(globalDefs, name, term),
            FluentIterable.concat(localDefs, ImmutableSet.of(name)).toSet(),
            asserted,
            lastAssumptions,
            responses);
      } else {
        var uf = mgr.getUFManager().declareUF(name, right, left.toArray(new FormulaType<?>[0]));
        return new SmtlibEvaluator(
            mode,
            solver,
            prover,
            closed,
            addFunction(globalDefs, name, p -> mgr.makeApplication(uf, p)),
            FluentIterable.concat(localDefs, ImmutableSet.of(name)).toSet(),
            asserted,
            lastAssumptions,
            responses);
      }
    }

    @Override
    public SmtlibEvaluator visitDefine(SmtlibParser.DefineContext ctx) {
      var name = getSymbolValue(ctx.symbol());
      checkArgument(!localDefs.contains(name), "Symbol %s already exists", name);
      var sort = sortEvaluator.visit(ctx.sort());
      var parameters = ctx.sortedVar();
      if (parameters.isEmpty()) {
        var term = new ExprEvaluator(globalDefs).visit(ctx.expr());
        checkArgument(mgr.getFormulaType(term).equals(sort));
        return new SmtlibEvaluator(
            mode,
            solver,
            prover,
            closed,
            addConstant(globalDefs, name, term),
            FluentIterable.concat(localDefs, ImmutableSet.of(name)).toSet(),
            asserted,
            lastAssumptions,
            responses);
      } else {
        var capture = globalDefs;
        // TODO Evaluate once during creation to catch any errors right away
        return new SmtlibEvaluator(
            mode,
            solver,
            prover,
            closed,
            addFunction(
                globalDefs,
                name,
                p -> {
                  checkArgument(p.size() == parameters.size());
                  var updated = capture;
                  for (int i = 0; i < p.size(); i++) {
                    var nameArg = getSymbolValue(parameters.get(i).symbol());
                    var sortArg = sortEvaluator.visit(parameters.get(i).sort());
                    var value = p.get(i);
                    // FIXME Probably too strong for bv/fp sorts?
                    checkArgument(mgr.getFormulaType(value).equals(sortArg));
                    updated = addConstant(updated, nameArg, value);
                  }
                  return new ExprEvaluator(updated).visit(ctx.expr());
                }),
            FluentIterable.concat(localDefs, ImmutableSet.of(name)).toSet(),
            asserted,
            lastAssumptions,
            responses);
      }
    }

    @Override
    public SmtlibEvaluator visitPush(SmtlibParser.PushContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'push' is not allowed in term mode");
      var levels = Integer.parseInt(ctx.Numeral().getText());
      ImmutableList.Builder<List<BooleanFormula>> newAsserted = ImmutableList.builder();
      newAsserted.addAll(asserted);
      for (var i = 0; i < levels; i++) {
        try {
          prover.push();
          newAsserted.add(ImmutableList.of());

        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          newAsserted.build(),
          Optional.empty(),
          responses);
    }

    @Override
    public SmtlibEvaluator visitPop(SmtlibParser.PopContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'pop' is not allowed in term mode");
      var levels = Integer.parseInt(ctx.Numeral().getText());
      checkArgument(levels < asserted.size());
      for (var i = 0; i < levels; i++) {
        prover.pop();
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted.subList(0, asserted.size() - levels),
          Optional.empty(),
          responses);
    }

    @Override
    public SmtlibEvaluator visitAssert(SmtlibParser.AssertContext ctx) {
      var term = (BooleanFormula) new ExprEvaluator(globalDefs).visit(ctx.expr());
      var last = asserted.get(asserted.size() - 1);
      var init = asserted.subList(0, asserted.size() - 1);
      var added = Stream.concat(last.stream(), Stream.of(term)).toList();
      try {
        prover.addConstraint(term);
      } catch (InterruptedException e) {
        sneakyThrow(e);
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          Stream.concat(init.stream(), Stream.of(added)).toList(),
          lastAssumptions,
          responses);
    }

    @Override
    public SmtlibEvaluator visitGetAssertions(SmtlibParser.GetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.TERM, "Command 'get-assertions' is not allowed in term mode");
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses.add(new FormulaManager.SolverResponse.AssertedResponse(getAssertions())));
    }

    @Override
    public SmtlibEvaluator visitCheckSat(SmtlibParser.CheckSatContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'check-sat' is not allowed in term mode");
      var status = Status.UNKNOWN;
      try {
        status = prover.isUnsat() ? Status.UNSAT : Status.SAT;
      } catch (SolverException e) {
        // Return 'unknown' when there is a solver exception
      } catch (InterruptedException e) {
        sneakyThrow(e);
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          Optional.empty(),
          responses.add(new FormulaManager.SolverResponse.CheckSatResponse(status)));
    }

    @Override
    public SmtlibEvaluator visitCheckSatAssuming(SmtlibParser.CheckSatAssumingContext ctx) {
      checkArgument(
          mode != ParsingMode.TERM, "Command 'check-sat-assuming' is not allowed in term mode");
      var assumed =
          ctx.expr().stream()
              .map(expr -> (BooleanFormula) new ExprEvaluator(globalDefs).visit(expr))
              .toList();

      var status = Status.UNKNOWN;
      try {
        status = prover.isUnsatWithAssumptions(assumed) ? Status.UNSAT : Status.SAT;
      } catch (SolverException e) {
        // Return 'unknown' when there is a solver exception
      } catch (InterruptedException e) {
        sneakyThrow(e);
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          Optional.of(assumed),
          responses.add(new FormulaManager.SolverResponse.CheckSatResponse(status)));
    }

    @Override
    public SmtlibEvaluator visitGetModel(SmtlibParser.GetModelContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'get-model' is not allowed in term mode");
      try (var model = prover.getModel()) {
        return new SmtlibEvaluator(
            mode,
            solver,
            prover,
            closed,
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions,
            responses.add(new FormulaManager.SolverResponse.ModelResponse(model.asList())));

      } catch (SolverException e) {
        sneakyThrow(e);
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetUnsatCore(SmtlibParser.GetUnsatCoreContext ctx) {
      checkArgument(
          mode != ParsingMode.TERM, "Command 'get-unsat-core' is not allowed in term mode");
      List<BooleanFormula> core = prover.getUnsatCore();
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses.add(new FormulaManager.SolverResponse.UnsatCoreResponse(core)));
    }

    @Override
    public SmtlibEvaluator visitGetUnsatAssumptions(SmtlibParser.GetUnsatAssumptionsContext ctx) {
      checkArgument(
          mode != ParsingMode.TERM, "Command 'get-unsat-assumptions' is not allowed in term mode");
      Optional<List<BooleanFormula>> core;
      try {
        core = prover.unsatCoreOverAssumptions(lastAssumptions.orElseThrow());
      } catch (SolverException | InterruptedException e) {
        sneakyThrow(e);
        throw new AssertionError();
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses.add(new FormulaManager.SolverResponse.UnsatCoreResponse(core.orElseThrow())));
    }

    @Override
    public SmtlibEvaluator visitGetValue(SmtlibParser.GetValueContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'get-value' is not allowed in term mode");
      var terms =
          ctx.expr().stream().map(expr -> new ExprEvaluator(globalDefs).visit(expr)).toList();

      ImmutableList.Builder<Formula> evaluated = ImmutableList.builder();
      for (var term : terms) {
        try (var evaluator = prover.getEvaluator()) {
          var newTerm = evaluator.eval(term);
          evaluated.add(newTerm == null ? term : newTerm);
        } catch (SolverException e) {
          sneakyThrow(e);
        }
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses.add(new FormulaManager.SolverResponse.EvaluationResponse(evaluated.build())));
    }

    @SuppressWarnings("resource")
    @Override
    public SmtlibEvaluator visitResetSolver(SmtlibParser.ResetSolverContext ctx) {
      checkArgument(mode != ParsingMode.TERM, "Command 'reset' is not allowed in term mode");
      prover.close();
      // Remove all symbols that were defined in this smtlib file from the context
      ImmutableMap.Builder<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
          nonlocal = ImmutableMap.builder();
      for (var symbol : globalDefs.keySet()) {
        if (!localDefs.contains(symbol)) {
          nonlocal.put(symbol, globalDefs.get(symbol));
        }
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          newProver(solver),
          closed,
          nonlocal.build(),
          ImmutableSet.of(),
          ImmutableList.of(ImmutableList.of()),
          Optional.empty(),
          responses);
    }

    @Override
    public SmtlibEvaluator visitResetAssertions(SmtlibParser.ResetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.TERM, "Command 'reset-assertions' is not allowed in term mode");
      for (var i = 0; i < asserted.size(); i++) {
        prover.pop();
      }
      try {
        // Restore empty base level
        prover.push();
      } catch (InterruptedException e) {
        sneakyThrow(e);
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          prover,
          closed,
          globalDefs,
          localDefs,
          ImmutableList.of(ImmutableList.of()),
          Optional.empty(),
          responses);
    }

    @Override
    public SmtlibEvaluator visitExit(SmtlibParser.ExitContext ctx) {
      return new SmtlibEvaluator(
          mode, solver, prover, true, globalDefs, localDefs, asserted, lastAssumptions, responses);
    }

    @Override
    public SmtlibEvaluator visitSmtlib(SmtlibParser.SmtlibContext ctx) {
      var eval = SmtlibEvaluator.this;
      try {
        for (var cmd : ctx.command()) {
          checkArgument(!eval.closed, "Can't run any more commands. Solver was closed");
          eval = eval.commandVisitor.visit(cmd);
        }
      } finally {
        prover.close();
      }
      return eval;
    }
  }

  private final CommandVisitor commandVisitor = new CommandVisitor();
}
