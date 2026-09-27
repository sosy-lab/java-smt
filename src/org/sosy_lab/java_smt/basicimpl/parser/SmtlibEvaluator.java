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
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.io.Serial;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Stream;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager.SolverResponse.CheckSatResponse.Status;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager;

/** Evaluates a Smtlib script after parsing. */
@SuppressWarnings("resource")
public final class SmtlibEvaluator {
  public static class SmtlibException extends IllegalArgumentException {
    @Serial private static final long serialVersionUID = -5011762550769108967L;

    SmtlibException(int line, String source, Throwable t) {
      super("Error in line %s:%n%s".formatted(line, source), t);
    }
  }

  /** Selects a sublanguage for the evaluator. */
  public enum ParsingMode {
    /**
     * Only allows a subset of Smtlib commands for formula parsing.
     *
     * <p>In formula mode only <code>(declare-const)</code>, <code>(dedine-const)</code>, <code>
     * (define-fun)</code>, <code>(define-fun)</code> and <code>(assert)</code> are allowed. Can be
     * used to deserialize a solver term that has been written out as Smtlib
     */
    FORMULA,
    /** Full Smtlib script will all commands that are found in the standard. */
    SCRIPT
  }

  /** Create a {@link FormulaType} from a Smtlib sort. */
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

  /** Create a {@link Formula} from a value expression in Smtlib. */
  class ConstEvaluator extends SmtlibBaseVisitor<Formula> {
    @Override
    public Formula visitBoolean(SmtlibParser.BooleanContext ctx) {
      return manager.getBooleanFormulaManager().makeBoolean(Boolean.parseBoolean(ctx.getText()));
    }

    private String toBinary(String bitvec) {
      String prefix = bitvec.substring(0, 2);
      String number = bitvec.substring(2);

      if (prefix.equals("#b")) {
        return number;
      } else {
        String binary = new BigInteger(number, 16).toString(2);
        return "0".repeat(4 * number.length() - binary.length()) + binary;
      }
    }

    @Override
    public Formula visitBitvec(SmtlibParser.BitvecContext ctx) {
      String binary = toBinary(ctx.getText());
      return manager
          .getBitvectorFormulaManager()
          .makeBitvector(binary.length(), new BigInteger(binary, 2));
    }

    @Override
    public Formula visitFloat(SmtlibParser.FloatContext ctx) {
      String b0 = toBinary(ctx.bitvec(0).getText());
      String b1 = toBinary(ctx.bitvec(1).getText());
      String b2 = toBinary(ctx.bitvec(2).getText());
      checkArgument(b0.length() == 1);
      return manager
          .getFloatingPointFormulaManager()
          .makeNumber(
              FloatingPointNumber.of(
                  b0 + b1 + b2,
                  FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit(
                      b1.length(), b2.length())));
    }

    @Override
    public Formula visitInteger(SmtlibParser.IntegerContext ctx) {
      return manager.getIntegerFormulaManager().makeNumber(getIntegerValue(ctx));
    }

    @Override
    public Formula visitReal(SmtlibParser.RealContext ctx) {
      return manager.getRationalFormulaManager().makeNumber(new BigDecimal(ctx.getText()));
    }

    @Override
    public Formula visitString(SmtlibParser.StringContext ctx) {
      String str = ctx.getText().substring(1, ctx.getText().length() - 1);
      return manager.getStringFormulaManager().makeString(str.replace("\"\"", "\""));
    }
  }

  /** Create a {@link Formula} from an expression in Smtlib. */
  class ExprEvaluator extends SmtlibBaseVisitor<Formula> {
    class FunctionEvaluator extends SmtlibBaseVisitor<Function<List<Formula>, Formula>> {
      @Override
      public Function<List<Formula>, Formula> visitVar(SmtlibParser.VarContext ctx) {
        return lookup(getSymbolValue(ctx.symbol())).apply(ImmutableList.of());
      }

      @Override
      public Function<List<Formula>, Formula> visitIndexed(SmtlibParser.IndexedContext ctx) {
        String symbol = getSymbolValue(ctx.symbol());
        if (symbol.matches("bv\\d+")) {
          // Special case: BV defines symbols (_ bvX m) to create bitvector literals. Here we
          // have to get the value of the bitvector straight from the symbol name
          checkArgument(ctx.integer().size() == 1);
          return p -> {
            checkArgument(p.isEmpty());
            return manager
                .getBitvectorFormulaManager()
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
        FormulaType<?> sort = sortEvaluator.visit(ctx.sort());
        checkArgument(sort.isArrayType());
        @SuppressWarnings("rawtypes")
        FormulaType.ArrayFormulaType arraySort = (FormulaType.ArrayFormulaType) sort;
        return value -> manager.getArrayFormulaManager().makeArray(arraySort, value.get(0));
      }
    }

    /**
     * Maps symbol names to definitions.
     *
     * <p>Contains theory symbols, as well as all user-defined symbols
     */
    private final PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
        context;

    private final FunctionEvaluator functionEvaluator = new FunctionEvaluator();

    ExprEvaluator(
        PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> pContext) {
      context = pContext;
    }

    /** Look up a symbol in the context to get its definition. */
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
      return constEvaluator.visit(ctx.children.get(0));
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
      PersistentMap<String, Void> letDefs = PathCopyingPersistentTreeMap.of();
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> newContext =
          context;
      for (SmtlibParser.BindingContext binding : ctx.binding()) {
        String sym = getSymbolValue(binding.symbol());
        checkArgument(
            !letDefs.containsKey(sym), "Let block contains more than one definition for %s", sym);
        letDefs = letDefs.putAndCopy(sym, null);
        Formula term = new ExprEvaluator(newContext).visit(binding.expr());
        newContext = addConstant(newContext, sym, term);
      }
      return new ExprEvaluator(newContext).visit(ctx.expr());
    }

    @Override
    public Formula visitQuantified(SmtlibParser.QuantifiedContext ctx) {
      ImmutableList.Builder<Formula> variables = ImmutableList.builder();
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> updated =
          context;
      for (SmtlibParser.SortedVarContext sortedVar : ctx.sortedVar()) {
        String name = getSymbolValue(sortedVar.symbol());
        FormulaType<?> sort = sortEvaluator.visit(sortedVar.sort());
        Formula term = manager.makeVariable(sort, genSymbol());
        updated = addConstant(updated, name, term);
        variables.add(term);
      }
      Formula evaluated = new ExprEvaluator(updated).visit(ctx.expr());
      checkArgument(evaluated instanceof BooleanFormula);
      BooleanFormula acc = (BooleanFormula) evaluated;
      for (Formula bound : variables.build().reverse()) {
        acc =
            manager
                .getQuantifiedFormulaManager()
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
      boolean app = true;
      for (SmtlibParser.ExprContext sub : ctx.expr()) {
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

  /** Add a function symbol to the context. */
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

  /** Add a constant symbol to the context. */
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

  class CommandVisitor extends SmtlibBaseVisitor<CommandVisitor> implements AutoCloseable {
    /** Prover state machine, similar to "solver execution modes" in Smtlib. */
    private interface ProverState {
      /**
       * Start state.
       *
       * <p>Entered at the start of the Smtlib script. Allows <code>(set-info></code>, <code>
       * (set-option)</code> and <code>(set-logic)</code>. Setting the logic will create a prover
       * and the state transitions to {@link ProverState.AssertState AssertState}. If {@link
       * ParsingMode#FORMULA ParsingMode.FORMULA} is used, no prover will be created and the state
       * machine never leaves the initial state
       */
      record StartState(Optional<String> logic, Set<SolverContext.ProverOptions> options)
          implements ProverState {}

      /**
       * Assert state.
       *
       * <p>Entered by <code>(set-logic)</code> and left when the prover is destroyed by <code>
       * (exit)</code> or <code>(reset)</code>. Allows all commands except <code>(set-logic)</code>
       * and <code>(set-option)</code> as the prover has already been initialized
       */
      record AssertState(ProverEnvironment prover) implements ProverState {}

      /**
       * Exit state.
       *
       * <p>Entered when <code>(exit)</code> has run
       */
      record ExitState() implements ProverState {}
    }

    private final ProverState state;
    private final PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
        globalDefs;
    private final PersistentMap<String, Object> localDefs;
    private final List<List<BooleanFormula>> asserted;
    private final Optional<List<BooleanFormula>> lastAssumptions;

    CommandVisitor(
        ProverState pState,
        PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
            pGlobalDefs,
        PersistentMap<String, Object> pLocalDefs,
        List<List<BooleanFormula>> pAsserted,
        Optional<List<BooleanFormula>> pLastAssumptions) {
      state = pState;
      globalDefs = pGlobalDefs;
      localDefs = pLocalDefs;
      asserted = pAsserted;
      lastAssumptions = pLastAssumptions;
    }

    CommandVisitor(
        PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
            pGlobalDefs) {
      this(
          new CommandVisitor.ProverState.StartState(Optional.empty(), ImmutableSet.of()),
          pGlobalDefs,
          PathCopyingPersistentTreeMap.of(),
          ImmutableList.of(ImmutableList.of()),
          Optional.empty());
    }

    /** Returns <code>true</code> once <code>(exit)</code> has closed the prover. */
    public boolean isClosed() {
      return state instanceof ProverState.ExitState;
    }

    @SuppressWarnings("unchecked")
    private static <E extends Throwable> void sneakyThrow(Throwable e) throws E {
      throw (E) e;
    }

    /** Open a new {@link ProverEnvironment} with the given {@link ProverOptions}. */
    private ProverEnvironment newProver(Set<SolverContext.ProverOptions> pOptions) {
      ProverEnvironment newProver =
          solver.newProverEnvironment(pOptions.toArray(new SolverContext.ProverOptions[] {}));
      try {
        // Start with one level, so that we can pop all formulas that will be added
        newProver.push();
      } catch (InterruptedException e) {
        sneakyThrow(e);
      }
      return newProver;
    }

    @Override
    public CommandVisitor visitSetInfo(SmtlibParser.SetInfoContext ctx) {
      // Skip info command
      return this;
    }

    /** Helper function to update an option set with a new setting. */
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
    public CommandVisitor visitSetOption(SmtlibParser.SetOptionContext ctx) {
      if (state instanceof ProverState.StartState startState) {
        String option = ctx.attribute().keyword().getText();
        ImmutableMap<String, SolverContext.ProverOptions> supportedOptions =
            ImmutableMap.of(
                ":produce-models",
                SolverContext.ProverOptions.GENERATE_MODELS,
                ":produce-unsat-assumptions",
                SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS,
                ":produce-unsat-cores",
                SolverContext.ProverOptions.GENERATE_UNSAT_CORE);
        if (supportedOptions.containsKey(option)) {
          String value = ctx.attribute().expr().getText();
          checkArgument(value.equals("true") || value.equals("false"));
          return new CommandVisitor(
              new ProverState.StartState(
                  startState.logic,
                  newOptionSet(
                      startState.options,
                      supportedOptions.get(option),
                      Boolean.parseBoolean(value))),
              globalDefs,
              localDefs,
              asserted,
              lastAssumptions);

        } else {
          // TODO Report that we skipped the option
          return this;
        }

      } else {
        throw new AssertionError("Can't set options. Solver already initialized");
      }
    }

    @Override
    public CommandVisitor visitSetLogic(SmtlibParser.SetLogicContext ctx) {
      if (state instanceof ProverState.StartState startState) {
        checkArgument(startState.logic.isEmpty(), "Logic has already been set");
        return new CommandVisitor(
            new ProverState.StartState(Optional.of(ctx.getText()), startState.options),
            globalDefs,
            localDefs,
            asserted,
            lastAssumptions);

      } else {
        throw new IllegalArgumentException("Solver is already running");
      }
    }

    @Override
    public CommandVisitor visitDeclare(SmtlibParser.DeclareContext ctx) {
      if (state instanceof ProverState.StartState startState && startState.logic.isEmpty()) {
        return new CommandVisitor(
                new ProverState.StartState(Optional.of("ALL"), startState.options),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else {
        String name = getSymbolValue(ctx.symbol());
        checkArgument(!localDefs.containsKey(name), "Symbol %s already exists", name);
        var sorts = transformedImmutableListCopy(ctx.sort(), sortEvaluator::visit);
        var left = sorts.subList(0, sorts.size() - 1);
        FormulaType<?> right = sorts.get(sorts.size() - 1);

        String localName = mode == ParsingMode.FORMULA ? name : name + genSymbol();
        if (sorts.size() == 1) {
          Formula term = manager.makeVariable(right, localName);
          return new CommandVisitor(
              state,
              addConstant(globalDefs, name, term),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions);
        } else {
          FunctionDeclaration<?> uf =
              manager.getUFManager().declareUF(name, right, left.toArray(new FormulaType<?>[0]));
          return new CommandVisitor(
              state,
              addFunction(globalDefs, name, p -> manager.makeApplication(uf, p)),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions);
        }
      }
    }

    @Override
    public CommandVisitor visitDefine(SmtlibParser.DefineContext ctx) {
      if (state instanceof ProverState.StartState startState && startState.logic.isEmpty()) {
        return new CommandVisitor(
                new ProverState.StartState(Optional.of("ALL"), startState.options),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else {
        String name = getSymbolValue(ctx.symbol());
        checkArgument(!localDefs.containsKey(name), "Symbol %s already exists", name);
        FormulaType<?> sort = sortEvaluator.visit(ctx.sort());
        List<SmtlibParser.SortedVarContext> parameters = ctx.sortedVar();
        if (parameters.isEmpty()) {
          Formula term = new ExprEvaluator(globalDefs).visit(ctx.expr());
          checkArgument(manager.getFormulaType(term).equals(sort));
          return new CommandVisitor(
              state,
              addConstant(globalDefs, name, term),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions);
        } else {
          PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> capture =
              globalDefs;
          return new CommandVisitor(
              state,
              addFunction(
                  globalDefs,
                  name,
                  p -> {
                    checkArgument(p.size() == parameters.size());
                    PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>>
                        updated = capture;
                    for (int i = 0; i < p.size(); i++) {
                      String nameArg = getSymbolValue(parameters.get(i).symbol());
                      FormulaType<?> sortArg = sortEvaluator.visit(parameters.get(i).sort());
                      Formula value = p.get(i);
                      checkArgument(manager.getFormulaType(value).equals(sortArg));
                      updated = addConstant(updated, nameArg, value);
                    }
                    return new ExprEvaluator(updated).visit(ctx.expr());
                  }),
              localDefs.putAndCopy(name, null),
              asserted,
              lastAssumptions);
        }
      }
    }

    @Override
    public CommandVisitor visitPush(SmtlibParser.PushContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'push' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        int levels = Integer.parseInt(ctx.Numeral().getText());
        ImmutableList.Builder<List<BooleanFormula>> newAsserted = ImmutableList.builder();
        newAsserted.addAll(asserted);
        for (int i = 0; i < levels; i++) {
          try {
            assertState.prover.push();
            newAsserted.add(ImmutableList.of());

          } catch (InterruptedException e) {
            sneakyThrow(e);
          }
        }
        return new CommandVisitor(
            state, globalDefs, localDefs, newAsserted.build(), Optional.empty());

      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitPop(SmtlibParser.PopContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'pop' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        int levels = Integer.parseInt(ctx.Numeral().getText());
        checkArgument(levels < asserted.size());
        for (int i = 0; i < levels; i++) {
          assertState.prover.pop();
        }
        return new CommandVisitor(
            state,
            globalDefs,
            localDefs,
            asserted.subList(0, asserted.size() - levels),
            Optional.empty());
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitAssert(SmtlibParser.AssertContext ctx) {
      BooleanFormula term = (BooleanFormula) new ExprEvaluator(globalDefs).visit(ctx.expr());
      if (mode == ParsingMode.SCRIPT) {
        if (state instanceof ProverState.StartState startState) {
          return new CommandVisitor(
                  new ProverState.AssertState(newProver(startState.options)),
                  globalDefs,
                  localDefs,
                  asserted,
                  lastAssumptions)
              .visit(ctx);

        } else if (state instanceof ProverState.AssertState assertState) {
          try {
            assertState.prover.addConstraint(term);
          } catch (InterruptedException e) {
            sneakyThrow(e);
          }
        } else {
          throw new AssertionError();
        }
      }
      List<BooleanFormula> last = asserted.get(asserted.size() - 1);
      List<List<BooleanFormula>> init = asserted.subList(0, asserted.size() - 1);
      List<BooleanFormula> added = Stream.concat(last.stream(), Stream.of(term)).toList();
      return new CommandVisitor(
          state,
          globalDefs,
          localDefs,
          Stream.concat(init.stream(), Stream.of(added)).toList(),
          lastAssumptions);
    }

    /** Returns a list of all assertions that are currently on the stack. */
    List<BooleanFormula> getAssertions() {
      ImmutableList.Builder<BooleanFormula> builder = ImmutableList.builder();
      for (List<BooleanFormula> level : asserted) {
        builder.addAll(level);
      }
      return builder.build();
    }

    @Override
    public CommandVisitor visitGetAssertions(SmtlibParser.GetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-assertions' is not allowed in formula mode");
      responseListener.accept(
          new FormulaManager.SolverResponse.AssertionsResponse(getAssertions()));
      return new CommandVisitor(state, globalDefs, localDefs, asserted, lastAssumptions);
    }

    @Override
    public CommandVisitor visitCheckSat(SmtlibParser.CheckSatContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'check-sat' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        Status status = null;
        try {
          status = assertState.prover.isUnsat() ? new Status.Unsat() : new Status.Sat();
        } catch (SolverException e) {
          status = new Status.Unknown(e.getMessage());
        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
        responseListener.accept(new FormulaManager.SolverResponse.CheckSatResponse(status));
        return new CommandVisitor(state, globalDefs, localDefs, asserted, Optional.empty());
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitCheckSatAssuming(SmtlibParser.CheckSatAssumingContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA,
          "Command 'check-sat-assuming' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        List<BooleanFormula> assumed =
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
        responseListener.accept(new FormulaManager.SolverResponse.CheckSatResponse(status));
        return new CommandVisitor(state, globalDefs, localDefs, asserted, Optional.of(assumed));
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitGetModel(SmtlibParser.GetModelContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-model' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        try (Model model = assertState.prover.getModel()) {
          responseListener.accept(new FormulaManager.SolverResponse.ModelResponse(model.asList()));
          return new CommandVisitor(state, globalDefs, localDefs, asserted, lastAssumptions);

        } catch (SolverException e) {
          sneakyThrow(e);
          throw new AssertionError();
        }
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitGetUnsatCore(SmtlibParser.GetUnsatCoreContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-unsat-core' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        List<BooleanFormula> core = assertState.prover.getUnsatCore();
        responseListener.accept(new FormulaManager.SolverResponse.UnsatCoreResponse(core));
        return new CommandVisitor(state, globalDefs, localDefs, asserted, lastAssumptions);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitGetUnsatAssumptions(SmtlibParser.GetUnsatAssumptionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA,
          "Command 'get-unsat-assumptions' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        Optional<List<BooleanFormula>> core;
        try {
          core = assertState.prover.unsatCoreOverAssumptions(lastAssumptions.orElseThrow());
        } catch (SolverException | InterruptedException e) {
          sneakyThrow(e);
          throw new AssertionError();
        }
        responseListener.accept(
            new FormulaManager.SolverResponse.UnsatCoreResponse(core.orElseThrow()));
        return new CommandVisitor(state, globalDefs, localDefs, asserted, lastAssumptions);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitGetValue(SmtlibParser.GetValueContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'get-value' is not allowed in formula mode");
      if (state instanceof ProverState.StartState startState) {
        return new CommandVisitor(
                new ProverState.AssertState(newProver(startState.options)),
                globalDefs,
                localDefs,
                asserted,
                lastAssumptions)
            .visit(ctx);

      } else if (state instanceof ProverState.AssertState assertState) {
        List<Formula> terms =
            ctx.expr().stream().map(expr -> new ExprEvaluator(globalDefs).visit(expr)).toList();

        ImmutableList.Builder<Formula> evaluated = ImmutableList.builder();
        for (Formula term : terms) {
          try (Evaluator evaluator = assertState.prover.getEvaluator()) {
            Formula newTerm = evaluator.eval(term);
            evaluated.add(newTerm == null ? term : newTerm);
          } catch (SolverException e) {
            sneakyThrow(e);
          }
        }
        responseListener.accept(
            new FormulaManager.SolverResponse.EvaluationResponse(evaluated.build()));
        return new CommandVisitor(state, globalDefs, localDefs, asserted, lastAssumptions);
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitResetSolver(SmtlibParser.ResetSolverContext ctx) {
      checkArgument(mode != ParsingMode.FORMULA, "Command 'reset' is not allowed in formula mode");
      if (state instanceof ProverState.AssertState assertState) {
        assertState.prover.close();
      }
      // Remove all symbols that were defined in this smtlib file from the context
      PersistentMap<String, Function<List<Integer>, Function<List<Formula>, Formula>>> nonlocal =
          PathCopyingPersistentTreeMap.of();
      for (Map.Entry<String, Function<List<Integer>, Function<List<Formula>, Formula>>> entry :
          globalDefs.entrySet()) {
        String symbol = entry.getKey();
        if (!localDefs.containsKey(symbol)) {
          nonlocal = nonlocal.putAndCopy(symbol, entry.getValue());
        }
      }
      return new CommandVisitor(
          new ProverState.StartState(Optional.empty(), ImmutableSet.of()),
          nonlocal,
          PathCopyingPersistentTreeMap.of(),
          ImmutableList.of(ImmutableList.of()),
          Optional.empty());
    }

    @Override
    public CommandVisitor visitResetAssertions(SmtlibParser.ResetAssertionsContext ctx) {
      checkArgument(
          mode != ParsingMode.FORMULA, "Command 'reset-assertions' is not allowed in formula mode");
      if (state instanceof ProverState.AssertState assertState) {
        for (int i = 0; i < asserted.size(); i++) {
          assertState.prover.pop();
        }
        try {
          // Restore empty base level
          assertState.prover.push();
        } catch (InterruptedException e) {
          sneakyThrow(e);
        }
        return new CommandVisitor(
            state, globalDefs, localDefs, ImmutableList.of(ImmutableList.of()), Optional.empty());
      } else {
        throw new AssertionError();
      }
    }

    @Override
    public CommandVisitor visitExit(SmtlibParser.ExitContext ctx) {
      if (state instanceof ProverState.AssertState assertState) {
        assertState.prover.close();
      }
      return new CommandVisitor(
          new ProverState.ExitState(), globalDefs, localDefs, asserted, lastAssumptions);
    }

    @Override
    public CommandVisitor visitSmtlib(SmtlibParser.SmtlibContext ctx) {
      CommandVisitor eval = this;
      try {
        for (SmtlibParser.CommandContext cmd : ctx.command()) {
          try {
            checkArgument(
                !(eval.state instanceof ProverState.ExitState),
                "Can't run any more commands. Solver was closed");
            eval = eval.visit(cmd);

          } catch (RuntimeException e) {
            int line = cmd.start.getLine();
            String source =
                cmd.start
                    .getInputStream()
                    .getText(new Interval(cmd.start.getStartIndex(), cmd.stop.getStopIndex()));
            throw new SmtlibException(line, source, e);
          }
        }
      } finally {
        eval.close();
      }
      return eval;
    }

    @Override
    public void close() {
      if (state instanceof ProverState.AssertState assertState) {
        assertState.prover.close();
      }
    }
  }

  private final ParsingMode mode;

  private final SolverContext solver;
  private final ParsingFormulaManager manager;

  private final SortEvaluator sortEvaluator = new SortEvaluator();
  private final ConstEvaluator constEvaluator = new ConstEvaluator();

  private final CommandVisitor commandVisitor;

  private final Consumer<FormulaManager.SolverResponse> responseListener;

  private static int counter = 0;

  public SmtlibEvaluator(
      ParsingMode pMode,
      SolverContext pSolver,
      ParsingFormulaManager pManager,
      Consumer<FormulaManager.SolverResponse> pResponseListener) {
    mode = pMode;
    solver = pSolver;
    manager = pManager;
    commandVisitor =
        new CommandVisitor(
            PathCopyingPersistentTreeMap.copyOf(
                new Predefined(pManager)
                    .addTheorySymbols()
                    .addUserSymbols(pManager.getDefinedSymbols())
                    .build()));
    responseListener = pResponseListener;
  }

  private SmtlibEvaluator(
      ParsingMode pMode,
      SolverContext pSolver,
      ParsingFormulaManager pManager,
      CommandVisitor pCommandVisitor,
      Consumer<FormulaManager.SolverResponse> pResponseListener) {
    mode = pMode;
    solver = pSolver;
    manager = pManager;
    commandVisitor = pCommandVisitor;
    responseListener = pResponseListener;
  }

  /** Generate a fresh variable name. */
  private static String genSymbol() {
    return String.format(".%s", counter++);
  }

  /** Parse an Smtlib integer value. */
  private static BigInteger getIntegerValue(SmtlibParser.IntegerContext ctx) {
    return new BigInteger(ctx.getText());
  }

  /** Parse a Smtlib symbol name and remove the quotes if necessary. */
  private static String getSymbolValue(SmtlibParser.SymbolContext ctx) {
    String str = ctx.getText();
    return str.charAt(0) == '|' ? str.substring(1, str.length() - 1) : str;
  }

  /** Run the evaluator for the given Smtlib input. */
  @CanIgnoreReturnValue
  public SmtlibEvaluator apply(ParseTree pSmtlib) {
    return new SmtlibEvaluator(
        mode, solver, manager, commandVisitor.visit(pSmtlib), responseListener);
  }

  /** Return a list of all assertions that are currently on the stack. */
  public List<BooleanFormula> getAssertions() {
    return commandVisitor.getAssertions();
  }
}
