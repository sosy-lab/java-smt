// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.CharMatcher;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableSet;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.basicimpl.tactics.NNFVisitor;
import org.sosy_lab.java_smt.utils.SolverUtils;

/** Common utilities for all solvers. */
public abstract class AbstractUnspecializedFormulaManager implements FormulaManager {

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

  @Override
  public final BooleanFormula applyTactic(BooleanFormula f, Tactic tactic)
      throws InterruptedException, SolverException {
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
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (this == otherManager) {
      return formula; // shortcut
    }
    return parse(otherManager.dumpFormula(formula).toString());
  }

  @Override
  public final <T extends Formula> T makeApplication(
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
