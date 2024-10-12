// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableMap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

/** FormulaManager class contains all operations which can be performed on formulas. */
public interface FormulaManager {

  /**
   * Parses an SMT-LIB2 String and translates it into an equivalent BooleanFormula constraint.
   *
   * @param pString SMT-LIB2 formula as String that will be parsed
   * @return BooleanFormula equivalent to the SMT-LIB2 string
   */
  // TODO Clean up exceptions?
  BooleanFormula universalParseFromString(String pString)
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException;

  /**
   * Calls the dumpSMTLIB2 method from the Generator, which will write the assembled SMT-LIB2 to a
   * file 'Out.smt2'.
   *
   * @throws IOException if writing to file fails
   */
  // TODO Return a String, instead of writing to a file
  void dumpSMTLIB2() throws IOException;

  /**
   * Returns the Integer-Theory. Because most SAT-solvers support automatic casting between Integer-
   * and Rational-Theory, the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL and others.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  IntegerFormulaManager getIntegerFormulaManager();

  /**
   * Returns the Rational-Theory. Because most SAT-solvers support automatic casting between
   * Integer- and Rational-Theory, the Integer- and the RationalFormulaManager both return the same
   * Formulas for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL, etc.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  RationalFormulaManager getRationalFormulaManager();

  /** Returns the Boolean-Theory. */
  BooleanFormulaManager getBooleanFormulaManager();

  /**
   * Returns the Array-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  ArrayFormulaManager getArrayFormulaManager();

  /**
   * Returns the Bitvector-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  BitvectorFormulaManager getBitvectorFormulaManager();

  /**
   * Returns the Floating-Point-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  FloatingPointFormulaManager getFloatingPointFormulaManager();

  /** Returns the function for dealing with uninterpreted functions (UFs). */
  UFManager getUFManager();

  /**
   * Returns the Seperation-Logic-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  SLFormulaManager getSLFormulaManager();

  /**
   * Returns the interface for handling quantifiers.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  QuantifiedFormulaManager getQuantifiedFormulaManager();

  /**
   * Returns the String Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  StringFormulaManager getStringFormulaManager();

  /**
   * Returns the Enumeration Theory, e.g., also known as 'limited domain'.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  EnumerationFormulaManager getEnumerationFormulaManager();

  /**
   * Create variable of the type equal to {@code formulaType}.
   *
   * @param formulaType the type of the variable.
   * @param name the name of the variable.
   * @return the created variable.
   */
  <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name);

  /**
   * Create a function application to the given list of arguments.
   *
   * @param declaration Function declaration
   * @param args List of arguments
   * @return Constructed formula
   */
  <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args);

  /**
   * Create a function application to the given list of arguments.
   *
   * @param declaration Function declaration
   * @param args List of arguments
   * @return Constructed formula
   */
  <T extends Formula> T makeApplication(FunctionDeclaration<T> declaration, Formula... args);

  /** Returns the type of the given Formula. */
  <T extends Formula> FormulaType<T> getFormulaType(T formula);

  /**
   * Parse a boolean formula given as a String in an SMTLIB file format. We expect exactly one
   * assertion to be contained in the query.
   *
   * <p>Example: <code>(declare-fun x () Int)(assert (= 0 x))</code>
   *
   * <p>It depends on the used SMT solver whether the given query must be self-contained and include
   * declarations for all used symbols or not, and also whether the query is allowed to contain
   * symbols with equal name, but different type/sort than existing symbols. The safest way is to
   * always declare all used symbols and to avoid conflicting types for them.
   *
   * <p>The behavior of the SMT solver is undefined if commands are provided in the SMTLIB-based
   * String that are different from declarations or an assertion, such as <code>push/pop</code> or
   * <code>set-info</code>. Most solvers just ignore those commands.
   *
   * <p>Variables that are defined, but not used in the assertion, might be ignored by the SMT
   * solver and they might not be available for later usage.
   *
   * @return A single formula from the assertion in the internal representation.
   * @throws IllegalArgumentException If the string cannot be parsed.
   */
  BooleanFormula parse(String s) throws IllegalArgumentException;

  /**
   * Serialize an input formula to an SMT-LIB format. Very useful when passing formulas between
   * different solvers.
   *
   * <p>To get a String, simply call {@link Object#toString()} on the returned object. This method
   * is lazy and does not create an output string until the returned object is actually used.
   *
   * @return SMT-LIB formula serialization.
   */
  Appender dumpFormula(BooleanFormula pT);

  /**
   * Apply a tactic which performs formula transformation. The available tactics depend on the used
   * solver.
   */
  BooleanFormula applyTactic(BooleanFormula input, Tactic tactic) throws InterruptedException;

  /**
   * Simplify an input formula, while ensuring equivalence.
   *
   * <p>For solvers that do not provide a simplification API, an original formula is returned.
   *
   * @param input The input formula
   * @return Simplified version of the formula
   */
  <T extends Formula> T simplify(T input) throws InterruptedException;

  /**
   * Visit the formula with a given visitor.
   *
   * <p>This method does <b>not recursively visit</b> sub-components of a formula its own, so the
   * given {@link FormulaVisitor} needs to call such visitation on its own.
   *
   * <p>Please be aware that calling this method might cause extensive stack usage depending on the
   * nesting of the given formula and the given {@link FormulaVisitor}. Additionally, sub-formulas
   * that are used several times in the formula might be visited several times. For an efficient
   * formula traversing, we also provide {@link #visitRecursively(Formula, FormulaVisitor)}.
   *
   * @param f formula to be visited
   * @param rFormulaVisitor an implementation that provides steps for each kind of formula.
   */
  @CanIgnoreReturnValue
  <R> R visit(Formula f, FormulaVisitor<R> rFormulaVisitor);

  /**
   * Visit the formula recursively with a given {@link FormulaVisitor}. This method traverses
   * sub-components of a formula automatically, depending on the return value of the {@link
   * TraversalProcess} in the given {@link FormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively, without using Java recursion,
   * and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula is visited
   * only once. Thus, it can be used to traverse DAG-like formulas efficiently.
   *
   * <p>The traversal is done in PRE-ORDER manner with regard to caching identical subtrees, i.e., a
   * parent will be visited BEFORE its children. The unmodified child-formulas are passed as
   * argument to the parent's visitation.
   */
  void visitRecursively(Formula f, FormulaVisitor<TraversalProcess> rFormulaVisitor);

  /**
   * Visit the formula recursively with a given {@link FormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively, without using Java recursion,
   * and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula is visited
   * only once. Thus, it can be used to traverse DAG-like formulas efficiently.
   *
   * <p>The traversal is done in POST-ORDER manner with regard to caching identical subtrees, i.e.,
   * a parent will be visited AFTER its children. The result of the child-visitation is passed as
   * argument to the parent's visitation.
   *
   * @param pFormulaVisitor Transformation described by the user.
   */
  <T extends Formula> T transformRecursively(T f, FormulaTransformationVisitor pFormulaVisitor);

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f The input formula
   * @return Map from variable names to the corresponding formulas.
   */
  ImmutableMap<String, Formula> extractVariables(Formula f);

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f The input formula
   * @return Map from variable names to the corresponding formulas. If an UF occurs multiple times
   *     in the input formula, an arbitrary instance of an application of this UF is in the map.
   */
  ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f);

  /**
   * Substitute every occurrence of any item from {@code changeFrom} in formula {@code f} to the
   * corresponding occurrence from {@code changeTo}.
   *
   * <p>E.g. if {@code changeFrom} contains a variable {@code a} and {@code changeTo} contains a
   * variable {@code b} all occurrences of {@code a} will be changed to {@code b} in the returned
   * formula.
   *
   * @param f Formula to change.
   * @param fromToMapping Mapping of old and new formula parts.
   * @return Formula with parts replaced.
   */
  <T extends Formula> T substitute(T f, Map<? extends Formula, ? extends Formula> fromToMapping);

  /**
   * Translates the formula from another context into the context represented by {@code this}.
   * Default implementation relies on string serialization ({@link #dumpFormula(BooleanFormula)} and
   * {@link #parse(String)}), but each solver may implement more efficient translation between its
   * own contexts.
   *
   * @param formula Formula belonging to {@code otherContext}.
   * @param otherManager Formula manager belonging to the other context.
   * @return Formula belonging to {@code this} context.
   */
  BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager);

  /**
   * Check whether the given String can be used as symbol/name for variables or undefined functions.
   *
   * <p>We explicitly state that with further development of SMT solvers and the SMTLib
   * specification, the list of forbidden variable names may change in the future. Users should if
   * possible not use logical or mathematical operators, or keywords strongly depending on SMTlib.
   *
   * <p>If a variable name is rejected, a possibility is escaping, e.g. either substituting the
   * whole variable name or just every invalid character with an escaped form. We recommend using an
   * escape sequence based on the token "JAVASMT", because it might be unusual enough to appear when
   * encoding a user's problem in SMT. Please note that you might also have to handle escaping the
   * escape sequence. Examples:
   *
   * <ul>
   *   <li>the invalid variable name <code>"="</code> (logical operator for equality) can be
   *       replaced with a string <code>"JAVASMT_EQUALS"</code>.
   *   <li>the invalid SMTlib-escaped variable name <code>"|test|"</code> (the solver SMTInterpol
   *       does not allow the pipe symbol <code>"|"</code> in names) can be replaced with <code>
   *       "JAVASMT_PIPEtestJAVASMT_PIPE"</code>.
   * </ul>
   */
  boolean isValidName(String variableName);

  /**
   * Get an escaped symbol/name for variables or undefined functions, if necessary.
   *
   * <p>See {@link #isValidName(String)} for further details.
   */
  String escape(String variableName);

  /**
   * Unescape the symbol/name for variables or undefined functions, if necessary.
   *
   * <p>The result is undefined for Strings that are not properly escaped.
   *
   * <p>See {@link #isValidName(String)} for further details.
   */
  String unescape(String variableName);
}
