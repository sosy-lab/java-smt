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

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.CharMatcher;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
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

  protected abstract TFormulaInfo parseImpl(String formulaStr) throws IllegalArgumentException;

  /**
   * Split up a sequence of lisp expressions.
   *
   * <p>This is used by {@link #parse(String)} as part of the preprocessing before the input is
   * passed on to the solver. SMT-LIB2 scripts are sequences of commands that are just r-expression.
   * We split them up and then return the list.
   *
   * <p>As an example <code>tokenize("(define-const a Int)(assert (= a 0)")</code> will return the
   * sequence <code>["(define-const a Int)", "(assert (= a 0))"]</code>
   */
  protected static List<String> tokenize(String input) {
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    boolean inComment = false;
    boolean inString = false;
    boolean inQuoted = false;

    int level = 0;

    StringBuilder token = new StringBuilder();
    for (int i = 0; i < input.length(); i++) {
      char c = input.charAt(i);
      if (inComment) {
        if (c == '\n') {
          // End of a comment
          inComment = false;
          if (level > 0) {
            // If we're in an expression we need to replace the entire comment (+ the newline) with
            // some whitespace. Otherwise symbols might get merged across line-wraps. This is not
            // a problem at the top-level where all terms are surrounded by brackets.
            token.append(' ');
          }
        }

      } else if (inString) {
        if (c == '"') {
          // We have a double quote: Check that it's not followed by another and actually closes
          // the string.
          Optional<Character> n =
              (i == input.length() - 1) ? Optional.empty() : Optional.of(input.charAt(i + 1));
          if (n.isEmpty() || n.orElseThrow() != '"') {
            // Close the string
            token.append(c);
            inString = false;
          } else {
            // Add both quotes to the token and skip one character ahead
            token.append(c);
            token.append(n.orElseThrow());
            i++;
          }
        } else {
          token.append(c);
        }

      } else if (inQuoted) {
        if (c == '|') {
          // Close the quotes
          inQuoted = false;
        }
        if (c == '\\') {
          // The SMT-LIB2 standard does not allow backslash inside quoted symbols:
          // Throw an exception
          throw new IllegalArgumentException();
        }
        token.append(c);

      } else if (c == ';') {
        // Start of a comment
        inComment = true;

      } else if (c == '"') {
        // Start of a string literal
        inString = true;
        token.append(c);

      } else if (c == '|') {
        // Start of a quoted symbol
        inQuoted = true;
        token.append(c);

      } else {
        // Just a regular character outside of comments, quotes or string literals
        if (level == 0) {
          // We're at the top-level
          if (!Character.isWhitespace(c)) {
            if (c == '(') {
              // Handle opening brackets
              token.append("(");
              level++;
            } else {
              // Should be unreachable: all top-level expressions need parentheses around them
              throw new IllegalArgumentException();
            }
          }
        } else {
          // We're inside an r-expression
          if (c != '\n') {
            // Append the letter to the token, unless it's a newline
            token.append(c);
          } else {
            // Replace newline with space
            token.append(' ');
          }
          // Handle opening/closing brackets
          if (c == '(') {
            level++;
          }
          if (c == ')') {
            if (level == 1) {
              builder.add(token.toString());
              token = new StringBuilder();
            }
            level--;
          }
        }
      }
    }
    if (level != 0) {
      // Throw an exception if the brackets don't match
      throw new IllegalArgumentException();
    }
    return builder.build();
  }

  /**
   * Check if the token is a function or variable declaration.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  protected static boolean isDeclarationToken(String token) {
    return token.matches("\\(\\s*(declare-const|declare-fun)[\\S\\s]*");
  }

  /**
   * Check if the token is a function definition.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  protected static boolean isDefinitionToken(String token) {
    return token.matches("\\(\\s*define-fun[\\S\\s]*");
  }

  /**
   * Check if the token is an <code>(assert ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  protected static boolean isAssertToken(String token) {
    return token.matches("\\(\\s*assert[\\S\\s]*");
  }

  /**
   * Check if the token is <code>(set-logic ..)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  protected static boolean isSetLogicToken(String token) {
    return token.matches("\\(\\s*set-logic[\\S\\s]*");
  }

  /**
   * Check if the token is <code>(exit ...)</code>.
   *
   * <p>Use {@link #tokenize(String)} to turn an SMT-LIB2 script into a string of input tokens.
   */
  protected static boolean isExitToken(String token) {
    return token.matches("\\(\\s*exit[\\S\\s]*");
  }

  /**
   * Takes a SMT-LIB2 script and cleans it up.
   *
   * <p>We remove all comments and put each command on its own line. Declarations and asserts are
   * kept and everything else is removed. For <code>(set-logic ..)</code> we make sure that it's at
   * the top of the file before removing it, and for <code>(exit)</code> we make sure that it can
   * only occur as the last command.
   */
  private String sanitize(String formulaStr) {
    List<String> tokens = tokenize(formulaStr);

    StringBuilder builder = new StringBuilder();
    int pos = 0; // index of the current token

    for (String token : tokens) {
      if (isSetLogicToken(token)) {
        // Skip the (set-logic ...) command at the beginning of the input
        Preconditions.checkArgument(pos == 0);

      } else if (isExitToken(token)) {
        // Skip any (exit) command at the end of the input
        Preconditions.checkArgument(pos == tokens.size() - 1);

      } else if (isDeclarationToken(token) || isDefinitionToken(token) || isAssertToken(token)) {
        // Keep only declaration, definitions and assertion
        builder.append(token).append('\n');

      } else {
        // Remove everything else
      }
      pos++;
    }
    return builder.toString();
  }

  @Override
  public BooleanFormula parse(String formulaStr) throws IllegalArgumentException {
    return formulaCreator.encapsulateBoolean(parseImpl(sanitize(formulaStr)));
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
  public BooleanFormula applyTactic(BooleanFormula f, Tactic tactic) throws InterruptedException {
    switch (tactic) {
      case ACKERMANNIZATION:
        return applyUFEImpl(f);
      case NNF:
        return applyNNFImpl(f);
      case TSEITIN_CNF:
        return applyCNFImpl(f);
      case QE_LIGHT:
        return applyQELightImpl(f);
      default:
        throw new UnsupportedOperationException("Unexpected enum value");
    }
  }

  /**
   * Eliminate UFs from the given input formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyUFEImpl(BooleanFormula pF) throws InterruptedException {
    return SolverUtils.ufElimination(this).eliminateUfs(pF);
  }

  /**
   * Eliminate quantifiers from the given input formula.
   *
   * <p>This is the light version that does not need to eliminate all quantifiers.
   *
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyQELightImpl(BooleanFormula pF) throws InterruptedException {

    // Returning the untouched formula is valid according to QE_LIGHT contract.
    // TODO: substitution-based implementation.
    return pF;
  }

  /**
   * Apply conjunctive normal form (CNF) transformation to the given input formula.
   *
   * @param pF Input to apply the CNF transformation to.
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyCNFImpl(BooleanFormula pF) throws InterruptedException {

    // TODO: generic implementation.
    throw new UnsupportedOperationException(
        "Currently there is no generic implementation for CNF conversion");
  }

  /**
   * Apply negation normal form (NNF) transformation to the given input formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected BooleanFormula applyNNFImpl(BooleanFormula input) throws InterruptedException {
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
    return makeApplication(declaration, Arrays.asList(args));
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
}
