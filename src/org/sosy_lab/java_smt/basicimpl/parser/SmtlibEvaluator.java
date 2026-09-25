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
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
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

@SuppressWarnings("resource")
public final class SmtlibEvaluator {
  public enum ParsingMode {
    FORMULA,
    SCRIPT
  }

  private interface ProverState {
    record StartState(Optional<String> logic, Set<SolverContext.ProverOptions> options)
        implements ProverState {}

    record AssertState(ProverEnvironment prover) implements ProverState {}

    record ExitState() implements ProverState {}
  }

  private final ParsingMode mode;
  private final SolverContext solver;
  private final FormulaManager mgr;
  private final ProverState state;

  private final PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
      globalDefs;
  private final PersistentMap<String, Object> localDefs;
  private final List<List<BooleanFormula>> asserted;
  private final Optional<List<BooleanFormula>> lastAssumptions;
  private final ImmutableList.Builder<FormulaManager.SolverResponse> responses;

  private static int counter = 0;

  @SuppressWarnings("checkstyle:parameternumber")
  private SmtlibEvaluator(
      ParsingMode pMode,
      SolverContext pSolver,
      ProverState pProverState,
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pGlobalDefs,
      PersistentMap<String, Object> pLocalDefs,
      List<List<BooleanFormula>> pAsserted,
      Optional<List<BooleanFormula>> pLastAssumptions,
      ImmutableList.Builder<FormulaManager.SolverResponse> pResponses) {
    mode = pMode;
    solver = pSolver;
    mgr = pSolver.getFormulaManager();
    state = pProverState;
    globalDefs = pGlobalDefs;
    localDefs = pLocalDefs;
    asserted = pAsserted;
    lastAssumptions = pLastAssumptions;
    responses = pResponses;
  }

  private static ProverEnvironment newProver(
      SolverContext pSolver, Set<SolverContext.ProverOptions> pOptions) {
    var newProver =
        pSolver.newProverEnvironment(pOptions.toArray(new SolverContext.ProverOptions[] {}));
    try {
      // Start with one level, so that we can pop all formulas that will be added
      newProver.push();
    } catch (InterruptedException e) {
      sneakyThrow(e);
    }
    return newProver;
  }

  public static SmtlibEvaluator link(
      SolverContext pSolver, ParsingFormulaManager pManager, ParsingMode pMode) {
    return new SmtlibEvaluator(
        pMode,
        pSolver,
        new ProverState.StartState(Optional.empty(), ImmutableSet.of()),
        PathCopyingPersistentTreeMap.copyOf(
            new Predefined(pManager)
                .addTheorySymbols()
                .addUserSymbols(pManager.getDefinedSymbols())
                .build()),
        PathCopyingPersistentTreeMap.of(),
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
    public FormulaType<?> visitSortString(SmtlibParser.SortStringContext ctx) {
      return FormulaType.StringType;
    }

    @Override
    public FormulaType<?> visitSortRegex(SmtlibParser.SortRegexContext ctx) {
      return FormulaType.RegexType;
    }

    @Override
    public FormulaType<?> visitSortBitvec(SmtlibParser.SortBitvecContext ctx) {
      return FormulaType.getBitvectorTypeWithSize(getIntegerValue(ctx.integer()).intValueExact());
    }

    @Override
    public FormulaType<?> visitSortRoundingMode(SmtlibParser.SortRoundingModeContext ctx) {
      return FormulaType.FloatingPointRoundingModeType;
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

  private final SortEvaluator sortEvaluator = new SortEvaluator();

  class ConstEvalator extends SmtlibBaseVisitor<Formula> {
    @Override
    public Formula visitBoolean(SmtlibParser.BooleanContext ctx) {
      return mgr.getBooleanFormulaManager().makeBoolean(Boolean.parseBoolean(ctx.getText()));
    }

    private String toBinary(String bitvec) {
      var prefix = bitvec.substring(0, 2);
      var number = bitvec.substring(2);

      if (prefix.equals("#b")) {
        return number;
      } else {
        var binary = new BigInteger(number, 16).toString(2);
        return "0".repeat(4 * number.length() - binary.length()) + binary;
      }
    }

    @Override
    public Formula visitBitvec(SmtlibParser.BitvecContext ctx) {
      var binary = toBinary(ctx.getText());
      return mgr.getBitvectorFormulaManager()
          .makeBitvector(binary.length(), new BigInteger(binary, 2));
    }

    @Override
    public Formula visitFloat(SmtlibParser.FloatContext ctx) {
      var b0 = toBinary(ctx.bitvec(0).getText());
      var b1 = toBinary(ctx.bitvec(1).getText());
      var b2 = toBinary(ctx.bitvec(2).getText());
      checkArgument(b0.length() == 1);
      return mgr.getFloatingPointFormulaManager()
          .makeNumber(
              FloatingPointNumber.of(
                  b0 + b1 + b2,
                  FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit(
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

    @Override
    public Formula visitString(SmtlibParser.StringContext ctx) {
      var str = ctx.getText().substring(1, ctx.getText().length() - 1);
      return mgr.getStringFormulaManager().makeString(str.replace("\"\"", "\""));
    }
  }

  private final ConstEvalator constEvalator = new ConstEvalator();

  class ExprEvaluator extends SmtlibBaseVisitor<Formula> {
    private final PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
        context;

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

    private final FunctionEvaluator functionEvaluator = new FunctionEvaluator();

    ExprEvaluator(
        PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pContext) {
      context = pContext;
    }

    private Function<List<Integer>, Function<List<Formula>, Formula>> lookup(String symbol) {
      if (!context.containsKey(symbol)) {
        throw new IllegalArgumentException(
            "Symbol `%s` is not defined. Context has %s"
                .formatted(
                    symbol,
                    context.isEmpty()
                        ? "no symbols"
                        : "symbols " + Joiner.on(", ").join(context.keySet())));
      }
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
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> local =
          PathCopyingPersistentTreeMap.of();
      for (var binding : ctx.binding()) {
        var sym = getSymbolValue(binding.symbol());
        checkArgument(
            !local.containsKey(sym), "Let block contains more than one definition for %s", sym);
        var term = visit(binding.expr());
        local = addConstant(local, sym, term);
      }
      var updated = context;
      for (var entry : local.entrySet()) {
        updated = updated.putAndCopy(entry.getKey(), entry.getValue());
      }
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
                        ? QuantifiedFormulaManager.Quantifier.EXISTS
                        : QuantifiedFormulaManager.Quantifier.FORALL,
                    ImmutableList.of(bound),
                    acc);
      }
      return acc;
    }

    @Override
    public Formula visitApp(SmtlibParser.AppContext ctx) {
      ImmutableList.Builder<Formula> builder = ImmutableList.builder();
      Function<List<Formula>, Formula> f = null;
      var app = true;
      for (var sub : ctx.expr()) {
        if (app) {
          f = functionEvaluator.visit(sub);
          app = false;
        } else {
          builder.add(visit(sub));
        }
      }
      if (f != null) {
        return f.apply(builder.build());
      } else {
        throw new AssertionError();
      }
    }
  }

  private static PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
      addFunction(
          PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> context,
          String name,
          Function<List<Formula>, Formula> function) {
    return context.putAndCopy(
        name,
        idx -> {
          checkArgument(idx.isEmpty());
          return function;
        });
  }

  private static PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
      addConstant(
          PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> context,
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

    private Set<SolverContext.ProverOptions> newOptionSet(
        Set<SolverContext.ProverOptions> optionSet,
        SolverContext.ProverOptions option,
        boolean value) {
      if (value) {
        return FluentIterable.concat(optionSet, ImmutableSet.of(option)).toSet();
      } else {
        return FluentIterable.from(optionSet).filter(v -> v != option).toSet();
      }
    }

    @Override
    public SmtlibEvaluator visitSetOption(SmtlibParser.SetOptionContext ctx) {
      if (state instanceof ProverState.StartState startState) {
        var option = ctx.attribute().keyword().getText();
        var supportedOptions =
            ImmutableMap.of(
                ":produce-models", SolverContext.ProverOptions.GENERATE_MODELS,
                ":produce-unsat-assumptions",
                    SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS,
                ":produce-unsat-cores", SolverContext.ProverOptions.GENERATE_UNSAT_CORE);
        if (supportedOptions.containsKey(option)) {
          var value = ctx.attribute().expr().getText();
          checkArgument(value.equals("true") || value.equals("false"));
          return new SmtlibEvaluator(
              mode,
              solver,
              new ProverState.StartState(
                  startState.logic,
                  newOptionSet(
                      startState.options,
                      supportedOptions.get(option),
                      Boolean.parseBoolean(value))),
              globalDefs,
              localDefs,
              asserted,
              lastAssumptions,
              responses);

        } else {
          // TODO Report that we skipped the option
          return SmtlibEvaluator.this;
        }

      } else {
        throw new AssertionError("Can't set options. Solver already initialized");
      }
    }

    @Override
    public SmtlibEvaluator visitSetLogic(SmtlibParser.SetLogicContext ctx) {
      if (state instanceof ProverState.StartState startState) {
        checkArgument(startState.logic.isEmpty(), "Logic has already been set");
        return new SmtlibEvaluator(
            mode,
            solver,
            new ProverState.StartState(Optional.of(ctx.getText()), startState.options),
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions,
            responses);

      } else {
        throw new IllegalArgumentException("Solver is already running");
      }
    }

    @Override
    public SmtlibEvaluator visitDeclare(SmtlibParser.DeclareContext ctx) {
      if (state instanceof ProverState.StartState startState && startState.logic.isEmpty()) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.StartState(Optional.of("ALL"), startState.options),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else {
        var name = getSymbolValue(ctx.symbol());
        checkArgument(!localDefs.containsKey(name), "Symbol %s already exists", name);
        var sorts = transformedImmutableListCopy(ctx.sort(), sortEvaluator::visit);
        var left = sorts.subList(0, sorts.size() - 1);
        var right = sorts.get(sorts.size() - 1);

        var localName = mode == ParsingMode.FORMULA ? name : name + genSymbol();
        if (sorts.size() == 1) {
          var term = mgr.makeVariable(right, localName);
          return new SmtlibEvaluator(
              mode,
              solver,
              state,
              addConstant(globalDefs, name, term),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions,
              responses);
        } else {
          var uf = mgr.getUFManager().declareUF(name, right, left.toArray(new FormulaType<?>[0]));
          return new SmtlibEvaluator(
              mode,
              solver,
              state,
              addFunction(globalDefs, name, p -> mgr.makeApplication(uf, p)),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions,
              responses);
        }
      }
    }

    @Override
    public SmtlibEvaluator visitDefine(SmtlibParser.DefineContext ctx) {
      if (state instanceof ProverState.StartState startState && startState.logic.isEmpty()) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.StartState(Optional.of("ALL"), startState.options),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else {
        var name = getSymbolValue(ctx.symbol());
        checkArgument(!localDefs.containsKey(name), "Symbol %s already exists", name);
        var sort = sortEvaluator.visit(ctx.sort());
        var parameters = ctx.sortedVar();
        if (parameters.isEmpty()) {
          var term = new ExprEvaluator(globalDefs).visit(ctx.expr());
          checkArgument(mgr.getFormulaType(term).equals(sort));
          return new SmtlibEvaluator(
              mode,
              solver,
              state,
              addConstant(globalDefs, name, term),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions,
              responses);
        } else {
          var capture = globalDefs;
          return new SmtlibEvaluator(
              mode,
              solver,
              state,
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
                      checkArgument(mgr.getFormulaType(value).equals(sortArg));
                      updated = addConstant(updated, nameArg, value);
                    }
                    return new ExprEvaluator(updated).visit(ctx.expr());
                  }),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions,
              responses);
        }
      }
    }

    @Override
    public SmtlibEvaluator visitPush(SmtlibParser.PushContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'push' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        var levels = Integer.parseInt(ctx.Numeral().getText());
        ImmutableList.Builder<List<BooleanFormula>> newAsserted = ImmutableList.builder();
        newAsserted.addAll(asserted);
        for (var i = 0; i < levels; i++) {
          try {
            assertState.prover.push();
            newAsserted.add(ImmutableList.of());

          } catch (InterruptedException e) {
            sneakyThrow(e);
          }
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            newAsserted.build(),
            Optional.empty(),
            responses);

      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitPop(SmtlibParser.PopContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'pop' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        var levels = Integer.parseInt(ctx.Numeral().getText());
        checkArgument(levels < asserted.size());
        for (var i = 0; i < levels; i++) {
          assertState.prover.pop();
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted.subList(0, asserted.size() - levels),
            Optional.empty(),
            responses);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitAssert(SmtlibParser.AssertContext ctx) {
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(
                    mode == ParsingMode.FORMULA ? null : newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        var term = (BooleanFormula) new ExprEvaluator(globalDefs).visit(ctx.expr());
        var last = asserted.get(asserted.size() - 1);
        var init = asserted.subList(0, asserted.size() - 1);
        var added = Stream.concat(last.stream(), Stream.of(term)).toList();
        if (mode == ParsingMode.SCRIPT) {
          try {
            assertState.prover.addConstraint(term);
          } catch (InterruptedException e) {
            sneakyThrow(e);
          }
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            Stream.concat(init.stream(), Stream.of(added)).toList(),
            lastAssumptions,
            responses);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetAssertions(SmtlibParser.GetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-assertions' is not allowed in formula mode");
      return new SmtlibEvaluator(
          mode,
          solver,
          state,
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses.add(new FormulaManager.SolverResponse.AssertedResponse(getAssertions())));
    }

    @Override
    public SmtlibEvaluator visitCheckSat(SmtlibParser.CheckSatContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'check-sat' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        Status status = null;
        try {
          status = assertState.prover.isUnsat() ? new Status.Unsat() : new Status.Sat();
        } catch (SolverException e) {
          status = new Status.Unknown(e.getMessage());
        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted,
            Optional.empty(),
            responses.add(new FormulaManager.SolverResponse.CheckSatResponse(status)));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitCheckSatAssuming(SmtlibParser.CheckSatAssumingContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA,
          "Command 'check-sat-assuming' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        var assumed =
            ctx.expr().stream()
                .map(expr -> (BooleanFormula) new ExprEvaluator(globalDefs).visit(expr))
                .toList();

        Status status = null;
        try {
          status =
              assertState.prover.isUnsatWithAssumptions(assumed)
                  ? new Status.Unsat()
                  : new Status.Sat();
        } catch (SolverException e) {
          status = new Status.Unknown(e.getMessage());
        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted,
            Optional.of(assumed),
            responses.add(new FormulaManager.SolverResponse.CheckSatResponse(status)));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetModel(SmtlibParser.GetModelContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-model' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        try (var model = assertState.prover.getModel()) {
          return new SmtlibEvaluator(
              mode,
              solver,
              state,
              globalDefs,
              localDefs,
              asserted,
              lastAssumptions,
              responses.add(new FormulaManager.SolverResponse.ModelResponse(model.asList())));

        } catch (SolverException e) {
          sneakyThrow(e);
          throw new AssertionError();
        }
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetUnsatCore(SmtlibParser.GetUnsatCoreContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-unsat-core' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        List<BooleanFormula> core = assertState.prover.getUnsatCore();
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions,
            responses.add(new FormulaManager.SolverResponse.UnsatCoreResponse(core)));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetUnsatAssumptions(SmtlibParser.GetUnsatAssumptionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA,
          "Command 'get-unsat-assumptions' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        Optional<List<BooleanFormula>> core;
        try {
          core = assertState.prover.unsatCoreOverAssumptions(lastAssumptions.orElseThrow());
        } catch (SolverException | InterruptedException e) {
          sneakyThrow(e);
          throw new AssertionError();
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions,
            responses.add(new FormulaManager.SolverResponse.UnsatCoreResponse(core.orElseThrow())));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitGetValue(SmtlibParser.GetValueContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-value' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new SmtlibEvaluator(
                mode,
                solver,
                new ProverState.AssertState(newProver(solver, startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions,
                responses)
            .commandVisitor.visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        var terms =
            ctx.expr().stream().map(expr -> new ExprEvaluator(globalDefs).visit(expr)).toList();

        ImmutableList.Builder<Formula> evaluated = ImmutableList.builder();
        for (var term : terms) {
          try (var evaluator = assertState.prover.getEvaluator()) {
            var newTerm = evaluator.eval(term);
            evaluated.add(newTerm == null ? term : newTerm);
          } catch (SolverException e) {
            sneakyThrow(e);
          }
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions,
            responses.add(new FormulaManager.SolverResponse.EvaluationResponse(evaluated.build())));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitResetSolver(SmtlibParser.ResetSolverContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'reset' is not allowed in formula mode");
      if (state instanceof ProverState.AssertState assertState) {
        assertState.prover.close();
      }
      // Remove all symbols that were defined in this smtlib file from the context
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> nonlocal =
          PathCopyingPersistentTreeMap.of();
      for (var entry : globalDefs.entrySet()) {
        var symbol = entry.getKey();
        if (!localDefs.containsKey(symbol)) {
          nonlocal = nonlocal.putAndCopy(symbol, entry.getValue());
        }
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          new ProverState.StartState(Optional.empty(), ImmutableSet.of()),
          nonlocal,
          PathCopyingPersistentTreeMap.of(),
          ImmutableList.of(ImmutableList.of()),
          Optional.empty(),
          responses);
    }

    @Override
    public SmtlibEvaluator visitResetAssertions(SmtlibParser.ResetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'reset-assertions' is not allowed in formula mode");
      if (state instanceof ProverState.AssertState assertState) {
        for (var i = 0; i < asserted.size(); i++) {
          assertState.prover.pop();
        }
        try {
          // Restore empty base level
          assertState.prover.push();
        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
        return new SmtlibEvaluator(
            mode,
            solver,
            state,
            globalDefs,
            localDefs,
            ImmutableList.of(ImmutableList.of()),
            Optional.empty(),
            responses);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public SmtlibEvaluator visitExit(SmtlibParser.ExitContext ctx) {
      if (state instanceof ProverState.AssertState assertState && assertState.prover != null) {
        assertState.prover.close();
      }
      return new SmtlibEvaluator(
          mode,
          solver,
          new ProverState.ExitState(),
          globalDefs,
          localDefs,
          asserted,
          lastAssumptions,
          responses);
    }

    @Override
    public SmtlibEvaluator visitSmtlib(SmtlibParser.SmtlibContext ctx) {
      var eval = SmtlibEvaluator.this;
      try {
        for (var cmd : ctx.command()) {
          checkArgument(
              !(eval.state instanceof ProverState.ExitState),
              "Can't run any more commands. Solver was closed");
          eval = eval.commandVisitor.visit(cmd);
        }
      } finally {
        if (eval.state instanceof ProverState.AssertState assertState) {
          if (assertState.prover != null) {
            assertState.prover.close();
          }
        }
      }
      return eval;
    }
  }

  private final CommandVisitor commandVisitor = new CommandVisitor();
}
