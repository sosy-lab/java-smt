/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

// Generated from Smtlib.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parser;

import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced by {@link
 * SmtlibParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for operations with no return
 *     type.
 */
public interface SmtlibVisitor<T> extends ParseTreeVisitor<T> {
  /**
   * Visit a parse tree produced by {@link SmtlibParser#boolean_}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitBoolean(SmtlibParser.BooleanContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#bitvec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitBitvec(SmtlibParser.BitvecContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#float_}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFloat(SmtlibParser.FloatContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#integer}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInteger(SmtlibParser.IntegerContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#real}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitReal(SmtlibParser.RealContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#literal}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLiteral(SmtlibParser.LiteralContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#symbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSymbol(SmtlibParser.SymbolContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#keyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitKeyword(SmtlibParser.KeywordContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortBool} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortBool(SmtlibParser.SortBoolContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortInt} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortInt(SmtlibParser.SortIntContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortReal} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortReal(SmtlibParser.SortRealContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortBitvec} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortBitvec(SmtlibParser.SortBitvecContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortFloat} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortFloat(SmtlibParser.SortFloatContext ctx);

  /**
   * Visit a parse tree produced by the {@code SortArray} labeled alternative in {@link
   * SmtlibParser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortArray(SmtlibParser.SortArrayContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#quantifier}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQuantifier(SmtlibParser.QuantifierContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#sortedVar}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortedVar(SmtlibParser.SortedVarContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#binding}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitBinding(SmtlibParser.BindingContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttribute(SmtlibParser.AttributeContext ctx);

  /**
   * Visit a parse tree produced by the {@code Const} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitConst(SmtlibParser.ConstContext ctx);

  /**
   * Visit a parse tree produced by the {@code Var} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVar(SmtlibParser.VarContext ctx);

  /**
   * Visit a parse tree produced by the {@code Indexed} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIndexed(SmtlibParser.IndexedContext ctx);

  /**
   * Visit a parse tree produced by the {@code As} labeled alternative in {@link SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAs(SmtlibParser.AsContext ctx);

  /**
   * Visit a parse tree produced by the {@code Annotated} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAnnotated(SmtlibParser.AnnotatedContext ctx);

  /**
   * Visit a parse tree produced by the {@code Let} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLet(SmtlibParser.LetContext ctx);

  /**
   * Visit a parse tree produced by the {@code Quantified} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQuantified(SmtlibParser.QuantifiedContext ctx);

  /**
   * Visit a parse tree produced by the {@code App} labeled alternative in {@link
   * SmtlibParser#expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitApp(SmtlibParser.AppContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#setInfo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetInfo(SmtlibParser.SetInfoContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#setOption}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetOption(SmtlibParser.SetOptionContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#setLogic}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetLogic(SmtlibParser.SetLogicContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#declare}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeclare(SmtlibParser.DeclareContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#define}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDefine(SmtlibParser.DefineContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#assert_}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAssert(SmtlibParser.AssertContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCommand(SmtlibParser.CommandContext ctx);

  /**
   * Visit a parse tree produced by {@link SmtlibParser#smtlib}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSmtlib(SmtlibParser.SmtlibContext ctx);
}
