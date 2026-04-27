// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.ASSERT_MODE;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.EXITED_STATE;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.RESULT_MODE;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.SAT_MODE;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.START_MODE;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.SMTLIB2ProgramState.UNSAT_MODE;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.CharMatcher;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.errorprone.annotations.ForOverride;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormulaManager;
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
@SuppressWarnings("ClassTypeParameterName")
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
      ImmutableSet.of("true", "false", "and", "or", "select", "store", "xor", "distinct", "let");

  /**
   * Avoid using escape characters of SMT-LIB2 as part of names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  private static final CharMatcher DISALLOWED_CHARACTERS = CharMatcher.anyOf("|\\");

  /** Mapping of disallowed char to their escaped counterparts. */
  /* Keep this map in sync with {@link #DISALLOWED_CHARACTERS}.
   * Counterparts can be any unique string. For optimization, we could even use plain chars. */
  @VisibleForTesting
  public static final ImmutableBiMap<Character, String> DISALLOWED_CHARACTER_REPLACEMENT =
      ImmutableBiMap.of('|', "pipe", '\\', "backslash");

  private static final char ESCAPE = '$'; // just some allowed symbol, can be any char

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

  private final @Nullable AbstractSLFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> slManager;

  private final @Nullable AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      strManager;

  private final @Nullable AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      enumManager;

  private final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator;

  /** Builds a solver from the given theory implementations. */
  @SuppressWarnings("checkstyle:parameternumber")
  protected AbstractFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator,
      AbstractUFManager<TFormulaInfo, ?, TType, TEnv> functionManager,
      AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> booleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          bitvectorManager,
      @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          floatingPointManager,
      @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          quantifiedManager,
      @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> arrayManager,
      @Nullable AbstractSLFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> slManager,
      @Nullable AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> strManager,
      @Nullable AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          enumManager) {

    this.arrayManager = arrayManager;
    this.quantifiedManager = quantifiedManager;
    this.functionManager = checkNotNull(functionManager, "function manager needed");
    this.booleanManager = checkNotNull(booleanManager, "boolean manager needed");
    this.integerManager = pIntegerManager;
    this.rationalManager = pRationalManager;
    this.bitvectorManager = bitvectorManager;
    this.floatingPointManager = floatingPointManager;
    this.slManager = slManager;
    this.strManager = strManager;
    this.enumManager = enumManager;
    this.formulaCreator = pFormulaCreator;

    checkArgument(
        booleanManager.getFormulaCreator() == formulaCreator
            && functionManager.getFormulaCreator() == formulaCreator
            && !(bitvectorManager != null && bitvectorManager.getFormulaCreator() != formulaCreator)
            && !(floatingPointManager != null
                && floatingPointManager.getFormulaCreator() != formulaCreator)
            && !(quantifiedManager != null
                && quantifiedManager.getFormulaCreator() != formulaCreator),
        "The creator instances must match across the managers!");
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
  public SLFormulaManager getSLFormulaManager() {
    if (slManager == null) {
      throw new UnsupportedOperationException("Solver does not support separation logic theory");
    }
    return slManager;
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

  @Override
  public StringFormulaManager getStringFormulaManager() {
    if (strManager == null) {
      throw new UnsupportedOperationException("Solver does not support string theory");
    }
    return strManager;
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    if (enumManager == null) {
      throw new UnsupportedOperationException("Solver does not support enumeration theory");
    }
    return enumManager;
  }

  /** Override if the solver API only supports binary equality. */
  @SuppressWarnings("unused")
  protected TFormulaInfo equalImpl(TFormulaInfo pArg1, TFormulaInfo pArgs) {
    throw new UnsupportedOperationException(
        "equalImpl(x, y) must be implemented in a subclass, if required.");
  }

  @Override
  public BooleanFormula makeEqual(Iterable<Formula> pArgs) {
    FluentIterable<TFormulaInfo> args = getTFormulaInfosForComparison(pArgs);
    return formulaCreator.encapsulateBoolean(equalImpl(args));
  }

  /** Override if the solver API supports equality with many arguments. */
  protected TFormulaInfo equalImpl(Iterable<TFormulaInfo> pArgs) {
    List<TFormulaInfo> equalities = new ArrayList<>();
    for (TFormulaInfo[] pair : pairwise(pArgs)) {
      equalities.add(equalImpl(pair[0], pair[1]));
    }
    return booleanManager.andImpl(equalities);
  }

  /** for an Iterable [1, 2, 3, 4, 5], collect pairs [(1,2), (2,3), (3,4), (4,5)]. */
  @SuppressWarnings("unchecked")
  private <T> List<T[]> pairwise(Iterable<T> pArgs) {
    final List<T[]> result = new ArrayList<>();
    T prev = null;
    for (T arg : pArgs) {
      if (prev != null) {
        result.add((T[]) new Object[] {prev, arg});
      }
      prev = arg;
    }
    return result;
  }

  @Override
  public BooleanFormula makeDistinct(Iterable<Formula> pArgs) {
    FluentIterable<TFormulaInfo> args = getTFormulaInfosForComparison(pArgs);
    return formulaCreator.encapsulateBoolean(distinctImpl(args));
  }

  @SuppressWarnings("unchecked")
  private FluentIterable<TFormulaInfo> getTFormulaInfosForComparison(Iterable<Formula> pArgs) {
    final ImmutableSet<FormulaType<Formula>> types =
        FluentIterable.from(pArgs).transform(formulaCreator::getFormulaType).toSet();
    Preconditions.checkArgument(
        types.size() < 2
            || ImmutableSet.of(FormulaType.IntegerType, FormulaType.RationalType).equals(types),
        "All arguments for comparison must have the same type, but found %s different types: %s",
        types.size(),
        types);
    FluentIterable<TFormulaInfo> args =
        FluentIterable.from(pArgs).transform(formulaCreator::extractInfo);
    if (types.contains(FormulaType.IntegerType) && types.contains(FormulaType.RationalType)) {
      // We can compare Integer and Rational terms, so we convert all terms to Rational
      args =
          args.transform(
              ((AbstractNumeralFormulaManager<TFormulaInfo, ?, ?, ?, ?, ?>)
                      getRationalFormulaManager())
                  ::toType);
    }
    return args;
  }

  /** Override if the solver API supports <code>distinct</code>. */
  protected TFormulaInfo distinctImpl(Iterable<TFormulaInfo> pArgs) {
    List<TFormulaInfo> inequalities = new ArrayList<>();
    for (TFormulaInfo[] pair : allUniquePairs(pArgs)) {
      inequalities.add(booleanManager.not(equalImpl(pair[0], pair[1])));
    }
    return booleanManager.andImpl(inequalities);
  }

  /** for an Iterable [1, 2, 3, 4], collect all pairs [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]. */
  @SuppressWarnings("unchecked")
  private <T> List<T[]> allUniquePairs(Iterable<T> pArgs) {
    final List<T[]> result = new ArrayList<>();
    final List<T> seenSoFar = new ArrayList<>(); // local cache for visited elements
    for (T current : pArgs) {
      for (T previous : seenSoFar) {
        result.add((T[]) new Object[] {previous, current});
      }
      seenSoFar.add(current);
    }
    return result;
  }

  @SuppressWarnings("unused")
  protected TFormulaInfo parseImpl(String formulaStr) throws IllegalArgumentException {
    throw new UnsupportedOperationException(
        "parseImpl(String) must be implemented in a subclass, if required.");
  }

  @ForOverride
  protected List<TFormulaInfo> parseAllImpl(String formulaStr) throws IllegalArgumentException {
    // The fallback implementation splits the input into declarations and assertions,
    // and parses each assertion separately,
    // which is not very efficient, but it works for simple cases and is better than nothing
    List<String> tokens = Tokenizer.tokenize(formulaStr);

    List<String> declarationTokens = tokens.stream().filter(Tokenizer::isDeclarationToken).toList();
    List<String> definitionTokens = tokens.stream().filter(Tokenizer::isDefinitionToken).toList();
    List<String> assertTokens = tokens.stream().filter(Tokenizer::isAssertToken).toList();
    String definitions =
        Joiner.on("").join(declarationTokens) + Joiner.on("").join(definitionTokens);

    return Collections3.transformedImmutableListCopy(
        assertTokens, assertion -> parseImpl(definitions + assertion));
  }

  /**
   * Takes an SMT-LIB2 script and cleans it up.
   *
   * <p>We remove all comments and put each command on its own line. Declarations and asserts are
   * kept and everything else is removed. For <code>(set-logic ..)</code> we make sure that it's at
   * the top of the file before removing it, and for <code>(exit)</code> we make sure that it can
   * only occur as the last command.
   */
  private String sanitize(String formulaStr) {
    List<String> tokens = Tokenizer.tokenize(formulaStr);

    StringBuilder builder = new StringBuilder();

    // SMTLIB2ProgramState tracks that the SMTLIB2 query conforms to the rules outlined in the
    // standard. SMTLIB2ProgramStateMachine models the
    SMTLIB2ProgramStateMachine smtLibStateMachine = new SMTLIB2ProgramStateMachine(false);

    for (String token : tokens) {
      if (Tokenizer.isSetInfoToken(token)) {
        // set-info call is allowed to be the very first command in the benchmark, but can also
        // appear repeatedly throughout a SMT2 program
        // Technically it is even required to be the very first command, and it must set the
        //  :smt-lib-version attribute. See SMT-LIB 2.7 §3.11.3
        // TODO: check that version >= 2 for attribute :smt-lib-version?
        smtLibStateMachine.applyGSIOCommand();

      } else if (Tokenizer.isSetLogicToken(token)) {
        // (set-logic ...) commands must appear before an assertion is made. They may appear
        // throughout an SMT-LIB2 program to set the 'current logic' to a new logic, but the 'reset'
        // command has to be used before doing so every time.
        // The logic 'ALL' is the logic describing all available logics of a solver.
        // The following commands are allowed to be used before the very first 'set-logic':
        // echo, reset, reset-assertions, get-info, get-option, set-info, set-option
        smtLibStateMachine.applySetLogicCommand();

      } else if (Tokenizer.isExitToken(token)) {
        // Skip the (exit) command at the end of the input
        smtLibStateMachine.applyExitCommand();

      } else if (Tokenizer.isDeclarationToken(token)
          || Tokenizer.isDefinitionToken(token)
          || Tokenizer.isAssertToken(token)) {
        // Keep only declaration, definitions and assertion
        smtLibStateMachine.applyAssertDeclareCommands();
        builder.append(token).append('\n');

      } else if (Tokenizer.isForbiddenToken(token)) {
        // Throw an exception if the script contains commands like (pop) or (reset) that change the
        // state of the assertion stack.
        // We could keep track of the state of the stack and only consider the formulas that remain
        // on the stack at the end of the script. However, this does not seem worth it at the
        // moment. If needed, this feature can still be added later.
        String message;
        if (Tokenizer.isPushToken(token)) {
          smtLibStateMachine.applyPCommand();
          message = "(push ...)";
        } else if (Tokenizer.isPopToken(token)) {
          smtLibStateMachine.applyPCommand();
          message = "(pop ...)";
        } else if (Tokenizer.isResetAssertionsToken(token)) {
          smtLibStateMachine.applyResetAssertionsCommand();
          message = "(reset-assertions)";
        } else if (Tokenizer.isResetToken(token)) {
          smtLibStateMachine.applyResetCommand();
          message = "(reset)";
        } else {
          // Should be unreachable
          throw new UnsupportedOperationException("Unknown token " + checkNotNull(token));
        }
        throw new IllegalArgumentException(
            "SMTLIB command '%s' is not supported when parsing formulas.".formatted(message));

      } else {
        // Remove everything else, such as unknown or solver-specific commands, comments, etc.
      }
    }

    return builder.toString();
  }

  @Override
  public List<BooleanFormula> parseAll(String formulaStr) throws IllegalArgumentException {
    return parseAllImpl(sanitize(formulaStr)).stream()
        .map(formulaCreator::encapsulateBoolean)
        .toList();
  }

  protected abstract String dumpFormulaImpl(TFormulaInfo t) throws IOException;

  @Override
  public Appender dumpFormula(BooleanFormula t) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String raw = dumpFormulaImpl(formulaCreator.extractInfo(t));
        out.append(sanitize(raw));
      }
    };
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
  public BooleanFormula applyTactic(BooleanFormula f, Tactic tactic)
      throws InterruptedException, SolverException {
    return switch (tactic) {
      case ACKERMANNIZATION -> applyUFEImpl(f);
      case NNF -> applyNNFImpl(f);
      case TSEITIN_CNF -> applyCNFImpl(f);
      case QE_LIGHT -> applyQELightImpl(f);
    };
  }

  /** Eliminate UFs from the given input formula. */
  protected BooleanFormula applyUFEImpl(BooleanFormula pF) {
    return SolverUtils.ufElimination(this).eliminateUfs(pF);
  }

  /**
   * Eliminate quantifiers from the given input formula.
   *
   * <p>This is the light version that does not need to eliminate all quantifiers.
   *
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyQELightImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {

    // Returning the untouched formula is valid according to QE_LIGHT contract.
    // TODO: substitution-based implementation.
    return pF;
  }

  /**
   * Apply conjunctive normal form (CNF) transformation to the given input formula.
   *
   * @param pF Input to apply the CNF transformation to.
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyCNFImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {

    // TODO: generic implementation.
    throw new UnsupportedOperationException(
        "Currently there is no generic implementation for CNF conversion");
  }

  /**
   * Apply negation normal form (NNF) transformation to the given input formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyNNFImpl(BooleanFormula input)
      throws InterruptedException, SolverException {
    return getBooleanFormulaManager().transformRecursively(input, new NNFVisitor(this));
  }

  @Override
  public <T extends Formula> T simplify(T f) throws InterruptedException {
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), simplify(extractInfo(f)));
  }

  /**
   * Apply a simplification procedure for the given formula.
   *
   * <p>This does not need to change something, but it might simplify the formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   */
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
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    ImmutableMap.Builder<String, Formula> found = ImmutableMap.builder();
    formulaCreator.extractVariablesAndUFs(f, false, found::put);
    return found.buildOrThrow(); // visitation should not visit any symbol twice
  }

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f The input formula
   */
  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    ImmutableMap.Builder<String, Formula> found = ImmutableMap.builder();
    formulaCreator.extractVariablesAndUFs(f, true, found::put);
    // We can find duplicate keys with different values, like UFs with distinct parameters.
    // In such a case, we use only one appearance (the last one).
    return found.buildKeepingLast();
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (this == otherManager) {
      return formula; // shortcut
    }
    return parse(otherManager.dumpFormula(formula).toString());
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    checkVariableName(name);
    Formula t;
    if (formulaType.isBooleanType()) {
      t = booleanManager.makeVariable(name);
    } else if (formulaType.isIntegerType()) {
      assert integerManager != null;
      t = integerManager.makeVariable(name);
    } else if (formulaType.isRationalType()) {
      assert rationalManager != null;
      t = rationalManager.makeVariable(name);
    } else if (formulaType.isStringType()) {
      assert strManager != null;
      t = strManager.makeVariable(name);
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

    if (declaration.getKind() == FunctionDeclarationKind.CONST) {
      ArrayFormulaType<?, ?> arrayType = (ArrayFormulaType<?, ?>) declaration.getType();
      Formula defaultElement = Iterables.getOnlyElement(args);
      return (T)
          arrayManager.makeArray(
              arrayType.getIndexType(),
              getFormulaType(defaultElement),
              Iterables.getOnlyElement(args));
    }

    return formulaCreator.callFunction(declaration, args);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, ImmutableList.copyOf(args));
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
  public final boolean isValidName(String pVar) {
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
  @VisibleForTesting
  public static void checkVariableName(final String variableName) {
    final String help = "Use FormulaManager#isValidName to check your identifier before using it.";
    Preconditions.checkArgument(
        !variableName.isEmpty(), "Identifier for variable should not be empty.");
    Preconditions.checkArgument(
        !BASIC_OPERATORS.contains(variableName),
        "Identifier '%s' can not be used, because it is a simple operator. %s",
        variableName,
        help);
    Preconditions.checkArgument(
        !SMTLIB2_KEYWORDS.contains(variableName),
        "Identifier '%s' can not be used, because it is a keyword of SMT-LIB2. %s",
        variableName,
        help);
    Preconditions.checkArgument(
        DISALLOWED_CHARACTERS.matchesNoneOf(variableName),
        "Identifier '%s' can not be used, "
            + "because it should not contain an escape character %s of SMT-LIB2. %s",
        variableName,
        DISALLOWED_CHARACTER_REPLACEMENT
            .keySet(), // toString prints UTF8-encoded escape sequence, better than nothing.
        help);
  }

  /* This escaping works for simple escape sequences only, i.e., keywords are unique enough. */
  @Override
  public final String escape(String pVar) {
    // as long as keywords stay simple, this simple escaping is sufficient
    if (pVar.isEmpty() || BASIC_OPERATORS.contains(pVar) || SMTLIB2_KEYWORDS.contains(pVar)) {
      return ESCAPE + pVar;
    }
    if (pVar.indexOf(ESCAPE) != -1) {
      pVar = pVar.replace("" + ESCAPE, "" + ESCAPE + ESCAPE);
    }
    if (DISALLOWED_CHARACTERS.matchesAnyOf(pVar)) {
      for (Map.Entry<Character, String> e : DISALLOWED_CHARACTER_REPLACEMENT.entrySet()) {
        pVar = pVar.replace(e.getKey().toString(), ESCAPE + e.getValue());
      }
    }
    return pVar; // unchanged
  }

  /* This unescaping works for simple escape sequences only, i.e., keywords are unique enough. */
  @Override
  public final String unescape(String pVar) {
    int idx = pVar.indexOf(ESCAPE);
    if (idx != -1) {
      // unescape BASIC_OPERATORS and SMTLIB2_KEYWORDS
      if (idx == 0) {
        String tmp = pVar.substring(1);
        if (tmp.isEmpty() || BASIC_OPERATORS.contains(tmp) || SMTLIB2_KEYWORDS.contains(tmp)) {
          return tmp;
        }
      }

      // unescape DISALLOWED_CHARACTERS
      StringBuilder str = new StringBuilder();
      int i = 0;
      while (i < pVar.length()) {
        if (pVar.charAt(i) == ESCAPE) {
          if (pVar.charAt(i + 1) == ESCAPE) {
            str.append(ESCAPE);
            i++;
          } else {
            String rest = pVar.substring(i + 1);
            for (Map.Entry<Character, String> e : DISALLOWED_CHARACTER_REPLACEMENT.entrySet()) {
              if (rest.startsWith(e.getValue())) {
                str.append(e.getKey());
                i += e.getValue().length();
                break;
              }
            }
          }
        } else {
          str.append(pVar.charAt(i));
        }
        i++;
      }
      return str.toString();
    }
    return pVar; // unchanged
  }

  public enum SMTLIB2ProgramState {
    /** Initial state. Can be re-entered using the 'reset' command. */
    START_MODE,
    /**
     * Mode entered after the initial setup is done by executing the 'set-logic' command. In this
     * state, formulas can be defined/asserted etc.
     */
    ASSERT_MODE,
    /** Mode entered after SAT has been returned after calling 'check-set'. */
    SAT_MODE,
    /** Mode entered after UNSAT has been returned after calling 'check-set'. */
    UNSAT_MODE,
    /**
     * Joined alternative to SAT_MODE and UNSAT_MODE. Used if we don't solve, i.e. don't know
     * whether we are in a SAT/UNSAT state after 'check-sat'.
     */
    RESULT_MODE,
    /**
     * State after 'exit' has been called. No operations are possible anymore and everything ends in
     * an error.
     */
    EXITED_STATE
  }

  /**
   * As defined by the <a
   * href="https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf">SMT-LIB2 standard</a>
   * an SMT-LIB2 program is allowed to utilize certain commands only if certain preconditions are
   * met. This state-machine models this in two ways:
   *
   * <p>- a lenient parse mode, that replaces the SAT_MODE and UNSAT_MODE with a joined RESULT_MODE,
   * as we are only interested in the resulting {@link BooleanFormula}s and don't solve the queries,
   * hence we can't decide whether we are in SAT/UNSAT_MODE.
   *
   * <p>- parsing including solving utilizes the SAT_MODE and UNSAT_MODE after 'check-sat'.
   *
   * <p>All methods return either the new state (which may be equal to the old), or throw a {@link
   * IllegalArgumentException} with an error message explaining the problem.
   */
  static class SMTLIB2ProgramStateMachine {

    private SMTLIB2ProgramState state = START_MODE;

    private final boolean strictLogicSelectionRequired;

    // TODO: track current logic
    // private LOGIC currentLogic;

    private static final String EXIT_ERROR_MSG =
        "It is not allowed to call any more SMT-LIB2 commands " + "after 'exit' has been used";

    /**
     * Creates a new SMTLIB2ProgramStateMachine for a new SMTLIB2 query (parsing or dumping).
     *
     * @param pRequiresStrictLogicSelection if false, no logic has to be set before switching to
     *     assertion mode, assuming logic 'ALL' implicitly. If true, logic selection is strictly
     *     required before defining, declaring or asserting terms etc., as specified by the SMT-LIB2
     *     standard.
     */
    SMTLIB2ProgramStateMachine(boolean pRequiresStrictLogicSelection) {
      strictLogicSelectionRequired = pRequiresStrictLogicSelection;
    }

    /**
     * Transitions into the SMTLIB2 program state after the 'exit' command, that disallows any
     * further commands.
     */
    void applyExitCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      state = EXITED_STATE;
    }

    /**
     * Used to get the new SMTLIB2 program state for commands: 'declare-*', 'define-*', and
     * 'assert'.
     */
    void applyAssertDeclareCommands() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      if (state != START_MODE) {
        state = ASSERT_MODE;
      } else if (!strictLogicSelectionRequired) {
        checkArgument(state == START_MODE);
        // Not part of the logic above as we still want to reject later 'set-logic' commands!
        state = ASSERT_MODE;
      } else {
        throw new IllegalArgumentException(
            "SMT-LIB2 command 'assert', or any of the 'declare-*' and 'define-*' commands are only"
                + " allowed to be used after a logic has been set via the 'set-logic' command");
      }
    }

    /** Used to get the new SMTLIB2 program state for command: 'check-sat'. */
    void applyCheckSatCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      if (state != START_MODE || !strictLogicSelectionRequired) {
        // Switches to SAT or UNSAT mode, but we don't solve, we parse,
        //  hence we use a collective state.
        // Also, if we allow implicit logic selection, no assertion is required for trivial results
        state = RESULT_MODE;
      } else {
        throw new IllegalArgumentException(
            "SMT-LIB2 command 'check-sat' is only allowed to be used after a logic has been set via"
                + " the 'set-logic' command");
      }
    }

    /**
     * Used to get the new SMTLIB2 program state for the 'echo' command. This options transition
     * always into the current state and calling this method is not necessary.
     */
    void applyEchoCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
    }

    /** Used to transition into the new SMTLIB2 program state for the 'get-assertion' command. */
    void applyGetAssertionCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      // Funnily, you are allowed to use 'get-assertion' without asserting something.
      // TODO: Section 4.1.7 of the standard (2.6) says:
      //  "The command can be issued only if the :produce-assertions option, which is set to
      //  false by default, is set to true."
      checkArgument(
          state != START_MODE || !strictLogicSelectionRequired,
          "SMT-LIB2 command 'get-assertion' is only allowed to be used after a logic has been set"
              + " via the 'set-logic' command");
      /*
      checkArgument(options.contains(PRODUCE_ASSERTIONS),
          "SMT-LIB2 command 'get-assertion' is only allowed to be used after the "
              + ":produce-assertions option has been set");
       */
    }

    /**
     * Used to transition into the new SMTLIB2 program state for commands: 'get-assignment',
     * 'get-model', and 'get-value'.
     */
    void applyGAMVCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      checkArgument(
          state == SAT_MODE || state == RESULT_MODE,
          "SMT-LIB2 commands 'get-model', 'get-assignment', and 'get-value' are only allowed to be"
              + " used after 'check-sat' has been called and returned SAT");
    }

    /**
     * Used to transition into the new SMTLIB2 program state for commands: 'get-info', 'get-option',
     * 'set-info', 'set-option'. These options transition always into the current state and calling
     * this method is not necessary.
     */
    void applyGSIOCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
    }

    /**
     * Used to transition into the new SMTLIB2 program state for commands: 'get-unsat-*',
     * 'get-proof'.
     */
    void applyGPUCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      checkArgument(
          state == UNSAT_MODE || state == RESULT_MODE,
          "SMT-LIB2 command 'get-proof' and all 'get-unsat-*' commands are only allowed to be"
              + " used after 'check-sat' has been called and returned UNSAT");
    }

    /** Used to transition into the new SMTLIB2 program state for the 'push' and 'pop' commands. */
    void applyPCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      if (state != START_MODE || !strictLogicSelectionRequired) {
        state = ASSERT_MODE;
      } else {
        throw new IllegalArgumentException(
            "SMT-LIB2 commands 'push' and 'pop' are only allowed to "
                + "be used once a logic has been set");
      }
    }

    /** Used to transition into the new SMTLIB2 program state for the 'reset' command. */
    void applyResetCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      state = START_MODE;
    }

    /** Used to transition into the new SMTLIB2 program state for the 'reset-assertions' command. */
    void applyResetAssertionsCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      if (state != START_MODE && state != ASSERT_MODE) {
        state = ASSERT_MODE;
      }
    }

    /** Used to transition into the new SMTLIB2 program state for the 'set-logic' command. */
    void applySetLogicCommand() {
      checkArgument(state != EXITED_STATE, EXIT_ERROR_MSG);
      if (state == START_MODE) {
        state = ASSERT_MODE;
      } else if (!strictLogicSelectionRequired) {
        // We allowed implicit logic selection and assumed 'ALL' already (by asserting or defining)
        throw new IllegalArgumentException(
            "SMT-LIB2 command 'set-logic' is not allowed to be used after declaring, defining or "
                + "asserting terms");
      } else {
        throw new IllegalArgumentException(
            "SMT-LIB2 command 'set-logic' is not allowed to be used more than once without calling"
                + " 'reset' first");
      }
    }
  }
}
