// Generated from
// /home/dalux/Dokumente/IdeaProjects/java-smt/
// src/org/sosy_lab/javaSmt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced by {@link
 * Smtlibv2Parser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for operations with no return
 *     type.
 */
public interface Smtlibv2Visitor<T> extends ParseTreeVisitor<T> {
  /**
   * Visit a parse tree produced by the {@code startlogic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStartlogic(Smtlibv2Parser.StartlogicContext ctx);

  /**
   * Visit a parse tree produced by the {@code starttheory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStarttheory(Smtlibv2Parser.StarttheoryContext ctx);

  /**
   * Visit a parse tree produced by the {@code startscript} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStartscript(Smtlibv2Parser.StartscriptContext ctx);

  /**
   * Visit a parse tree produced by the {@code startgenresp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStartgenresp(Smtlibv2Parser.StartgenrespContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#generalReservedWord}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGeneralReservedWord(Smtlibv2Parser.GeneralReservedWordContext ctx);

  /**
   * Visit a parse tree produced by the {@code simppresymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSimppresymb(Smtlibv2Parser.SimppresymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code simpundefsymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSimpundefsymb(Smtlibv2Parser.SimpundefsymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#quotedSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQuotedSymbol(Smtlibv2Parser.QuotedSymbolContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#predefSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPredefSymbol(Smtlibv2Parser.PredefSymbolContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#predefKeyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPredefKeyword(Smtlibv2Parser.PredefKeywordContext ctx);

  /**
   * Visit a parse tree produced by the {@code simpsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSimpsymb(Smtlibv2Parser.SimpsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code quotsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQuotsymb(Smtlibv2Parser.QuotsymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#numeral}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitNumeral(Smtlibv2Parser.NumeralContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#decimal}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecimal(Smtlibv2Parser.DecimalContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#hexadecimal}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitHexadecimal(Smtlibv2Parser.HexadecimalContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#binary}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitBinary(Smtlibv2Parser.BinaryContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#string}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitString(Smtlibv2Parser.StringContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#floatingpoint}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFloatingpoint(Smtlibv2Parser.FloatingpointContext ctx);

  /**
   * Visit a parse tree produced by the {@code prekey} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPrekey(Smtlibv2Parser.PrekeyContext ctx);

  /**
   * Visit a parse tree produced by the {@code keysimsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitKeysimsymb(Smtlibv2Parser.KeysimsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstantnum} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstantnum(Smtlibv2Parser.SpecconstantnumContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstantdec} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstantdec(Smtlibv2Parser.SpecconstantdecContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstanthex} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstanthex(Smtlibv2Parser.SpecconstanthexContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstantbin} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstantbin(Smtlibv2Parser.SpecconstantbinContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstantstring} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstantstring(Smtlibv2Parser.SpecconstantstringContext ctx);

  /**
   * Visit a parse tree produced by the {@code specconstantfloatingpoint} labeled alternative in
   * {@link Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpecconstantfloatingpoint(Smtlibv2Parser.SpecconstantfloatingpointContext ctx);

  /**
   * Visit a parse tree produced by the {@code sexprspec} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSexprspec(Smtlibv2Parser.SexprspecContext ctx);

  /**
   * Visit a parse tree produced by the {@code sexprsymb} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSexprsymb(Smtlibv2Parser.SexprsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code sexprkey} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSexprkey(Smtlibv2Parser.SexprkeyContext ctx);

  /**
   * Visit a parse tree produced by the {@code multisexpr} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMultisexpr(Smtlibv2Parser.MultisexprContext ctx);

  /**
   * Visit a parse tree produced by the {@code idxnum} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdxnum(Smtlibv2Parser.IdxnumContext ctx);

  /**
   * Visit a parse tree produced by the {@code idxsymb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdxsymb(Smtlibv2Parser.IdxsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code idsymb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdsymb(Smtlibv2Parser.IdsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code idsymbidx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdsymbidx(Smtlibv2Parser.IdsymbidxContext ctx);

  /**
   * Visit a parse tree produced by the {@code attrspec} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttrspec(Smtlibv2Parser.AttrspecContext ctx);

  /**
   * Visit a parse tree produced by the {@code attrsymb} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttrsymb(Smtlibv2Parser.AttrsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code attrsexpr} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttrsexpr(Smtlibv2Parser.AttrsexprContext ctx);

  /**
   * Visit a parse tree produced by the {@code attrkey} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttrkey(Smtlibv2Parser.AttrkeyContext ctx);

  /**
   * Visit a parse tree produced by the {@code attrkeyattr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttrkeyattr(Smtlibv2Parser.AttrkeyattrContext ctx);

  /**
   * Visit a parse tree produced by the {@code sortid} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortid(Smtlibv2Parser.SortidContext ctx);

  /**
   * Visit a parse tree produced by the {@code multisort} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMultisort(Smtlibv2Parser.MultisortContext ctx);

  /**
   * Visit a parse tree produced by the {@code qualid} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQualid(Smtlibv2Parser.QualidContext ctx);

  /**
   * Visit a parse tree produced by the {@code qualidsort} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQualidsort(Smtlibv2Parser.QualidsortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#varbinding}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVarbinding(Smtlibv2Parser.VarbindingContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sortedvar}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortedvar(Smtlibv2Parser.SortedvarContext ctx);

  /**
   * Visit a parse tree produced by the {@code patternsymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPatternsymb(Smtlibv2Parser.PatternsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code patternmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPatternmultisymb(Smtlibv2Parser.PatternmultisymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#matchcase}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMatchcase(Smtlibv2Parser.MatchcaseContext ctx);

  /**
   * Visit a parse tree produced by the {@code termspecconst} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermspecconst(Smtlibv2Parser.TermspecconstContext ctx);

  /**
   * Visit a parse tree produced by the {@code termqualid} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermqualid(Smtlibv2Parser.TermqualidContext ctx);

  /**
   * Visit a parse tree produced by the {@code multiterm} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMultiterm(Smtlibv2Parser.MultitermContext ctx);

  /**
   * Visit a parse tree produced by the {@code termlet} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermlet(Smtlibv2Parser.TermletContext ctx);

  /**
   * Visit a parse tree produced by the {@code termforall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermforall(Smtlibv2Parser.TermforallContext ctx);

  /**
   * Visit a parse tree produced by the {@code termexists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermexists(Smtlibv2Parser.TermexistsContext ctx);

  /**
   * Visit a parse tree produced by the {@code termmatch} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermmatch(Smtlibv2Parser.TermmatchContext ctx);

  /**
   * Visit a parse tree produced by the {@code termexclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTermexclam(Smtlibv2Parser.TermexclamContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sortsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortsymboldecl(Smtlibv2Parser.SortsymboldeclContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#metaspecconstant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMetaspecconstant(Smtlibv2Parser.MetaspecconstantContext ctx);

  /**
   * Visit a parse tree produced by the {@code funsymbspec} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunsymbspec(Smtlibv2Parser.FunsymbspecContext ctx);

  /**
   * Visit a parse tree produced by the {@code funsymbmeta} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunsymbmeta(Smtlibv2Parser.FunsymbmetaContext ctx);

  /**
   * Visit a parse tree produced by the {@code funsymbid} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunsymbid(Smtlibv2Parser.FunsymbidContext ctx);

  /**
   * Visit a parse tree produced by the {@code parfunsymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitParfunsymb(Smtlibv2Parser.ParfunsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code parfunmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitParfunmultisymb(Smtlibv2Parser.ParfunmultisymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code theorysort} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheorysort(Smtlibv2Parser.TheorysortContext ctx);

  /**
   * Visit a parse tree produced by the {@code theoryfun} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheoryfun(Smtlibv2Parser.TheoryfunContext ctx);

  /**
   * Visit a parse tree produced by the {@code theorysortdescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheorysortdescr(Smtlibv2Parser.TheorysortdescrContext ctx);

  /**
   * Visit a parse tree produced by the {@code theoryfundescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheoryfundescr(Smtlibv2Parser.TheoryfundescrContext ctx);

  /**
   * Visit a parse tree produced by the {@code theorydef} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheorydef(Smtlibv2Parser.TheorydefContext ctx);

  /**
   * Visit a parse tree produced by the {@code theoryval} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheoryval(Smtlibv2Parser.TheoryvalContext ctx);

  /**
   * Visit a parse tree produced by the {@code theorynotes} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheorynotes(Smtlibv2Parser.TheorynotesContext ctx);

  /**
   * Visit a parse tree produced by the {@code theoryattr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheoryattr(Smtlibv2Parser.TheoryattrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#theorydecl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheorydecl(Smtlibv2Parser.TheorydeclContext ctx);

  /**
   * Visit a parse tree produced by the {@code logictheory} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogictheory(Smtlibv2Parser.LogictheoryContext ctx);

  /**
   * Visit a parse tree produced by the {@code logiclanguage} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogiclanguage(Smtlibv2Parser.LogiclanguageContext ctx);

  /**
   * Visit a parse tree produced by the {@code logicext} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogicext(Smtlibv2Parser.LogicextContext ctx);

  /**
   * Visit a parse tree produced by the {@code logicval} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogicval(Smtlibv2Parser.LogicvalContext ctx);

  /**
   * Visit a parse tree produced by the {@code logicnotes} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogicnotes(Smtlibv2Parser.LogicnotesContext ctx);

  /**
   * Visit a parse tree produced by the {@code logicattr} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogicattr(Smtlibv2Parser.LogicattrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#logic}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic(Smtlibv2Parser.LogicContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sortdec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSortdec(Smtlibv2Parser.SortdecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#selectordec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSelectordec(Smtlibv2Parser.SelectordecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#constructordec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitConstructordec(Smtlibv2Parser.ConstructordecContext ctx);

  /**
   * Visit a parse tree produced by the {@code dataconstr} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDataconstr(Smtlibv2Parser.DataconstrContext ctx);

  /**
   * Visit a parse tree produced by the {@code datamultisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDatamultisymb(Smtlibv2Parser.DatamultisymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#functiondec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunctiondec(Smtlibv2Parser.FunctiondecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#functiondef}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunctiondef(Smtlibv2Parser.FunctiondefContext ctx);

  /**
   * Visit a parse tree produced by the {@code propsymb} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPropsymb(Smtlibv2Parser.PropsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code propnot} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPropnot(Smtlibv2Parser.PropnotContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#script}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitScript(Smtlibv2Parser.ScriptContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdassert}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdassert(Smtlibv2Parser.CmdassertContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdcheckSat}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdcheckSat(Smtlibv2Parser.CmdcheckSatContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdcheckSatAssuming}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdcheckSatAssuming(Smtlibv2Parser.CmdcheckSatAssumingContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddeclareConst}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddeclareConst(Smtlibv2Parser.CmddeclareConstContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatype}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddeclareDatatype(Smtlibv2Parser.CmddeclareDatatypeContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatypes}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddeclareDatatypes(Smtlibv2Parser.CmddeclareDatatypesContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddeclareFun}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddeclareFun(Smtlibv2Parser.CmddeclareFunContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddeclareSort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddeclareSort(Smtlibv2Parser.CmddeclareSortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddefineFun}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddefineFun(Smtlibv2Parser.CmddefineFunContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddefineFunRec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddefineFunRec(Smtlibv2Parser.CmddefineFunRecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddefineFunsRec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddefineFunsRec(Smtlibv2Parser.CmddefineFunsRecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmddefineSort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmddefineSort(Smtlibv2Parser.CmddefineSortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdecho}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdecho(Smtlibv2Parser.CmdechoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdexit}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdexit(Smtlibv2Parser.CmdexitContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetAssertions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetAssertions(Smtlibv2Parser.CmdgetAssertionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetAssignment}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetAssignment(Smtlibv2Parser.CmdgetAssignmentContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetInfo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetInfo(Smtlibv2Parser.CmdgetInfoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetModel}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetModel(Smtlibv2Parser.CmdgetModelContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetOption}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetOption(Smtlibv2Parser.CmdgetOptionContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetProof}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetProof(Smtlibv2Parser.CmdgetProofContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatAssumptions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetUnsatAssumptions(Smtlibv2Parser.CmdgetUnsatAssumptionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatCore}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetUnsatCore(Smtlibv2Parser.CmdgetUnsatCoreContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdgetValue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdgetValue(Smtlibv2Parser.CmdgetValueContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdpop}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdpop(Smtlibv2Parser.CmdpopContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdpush}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdpush(Smtlibv2Parser.CmdpushContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdreset}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdreset(Smtlibv2Parser.CmdresetContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdresetAssertions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdresetAssertions(Smtlibv2Parser.CmdresetAssertionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdsetInfo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdsetInfo(Smtlibv2Parser.CmdsetInfoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdsetLogic}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdsetLogic(Smtlibv2Parser.CmdsetLogicContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmdsetOption}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmdsetOption(Smtlibv2Parser.CmdsetOptionContext ctx);

  /**
   * Visit a parse tree produced by the {@code assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAssert(Smtlibv2Parser.AssertContext ctx);

  /**
   * Visit a parse tree produced by the {@code check} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCheck(Smtlibv2Parser.CheckContext ctx);

  /**
   * Visit a parse tree produced by the {@code checkassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCheckassume(Smtlibv2Parser.CheckassumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code declconst} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeclconst(Smtlibv2Parser.DeclconstContext ctx);

  /**
   * Visit a parse tree produced by the {@code decldata} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecldata(Smtlibv2Parser.DecldataContext ctx);

  /**
   * Visit a parse tree produced by the {@code decldatas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecldatas(Smtlibv2Parser.DecldatasContext ctx);

  /**
   * Visit a parse tree produced by the {@code declfun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeclfun(Smtlibv2Parser.DeclfunContext ctx);

  /**
   * Visit a parse tree produced by the {@code declsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeclsort(Smtlibv2Parser.DeclsortContext ctx);

  /**
   * Visit a parse tree produced by the {@code deffun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeffun(Smtlibv2Parser.DeffunContext ctx);

  /**
   * Visit a parse tree produced by the {@code deffunrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeffunrec(Smtlibv2Parser.DeffunrecContext ctx);

  /**
   * Visit a parse tree produced by the {@code deffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDeffunsrec(Smtlibv2Parser.DeffunsrecContext ctx);

  /**
   * Visit a parse tree produced by the {@code defsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDefsort(Smtlibv2Parser.DefsortContext ctx);

  /**
   * Visit a parse tree produced by the {@code echo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitEcho(Smtlibv2Parser.EchoContext ctx);

  /**
   * Visit a parse tree produced by the {@code exit} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitExit(Smtlibv2Parser.ExitContext ctx);

  /**
   * Visit a parse tree produced by the {@code getassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetassert(Smtlibv2Parser.GetassertContext ctx);

  /**
   * Visit a parse tree produced by the {@code getassign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetassign(Smtlibv2Parser.GetassignContext ctx);

  /**
   * Visit a parse tree produced by the {@code getinfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetinfo(Smtlibv2Parser.GetinfoContext ctx);

  /**
   * Visit a parse tree produced by the {@code getmodel} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetmodel(Smtlibv2Parser.GetmodelContext ctx);

  /**
   * Visit a parse tree produced by the {@code getoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetoption(Smtlibv2Parser.GetoptionContext ctx);

  /**
   * Visit a parse tree produced by the {@code getproof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetproof(Smtlibv2Parser.GetproofContext ctx);

  /**
   * Visit a parse tree produced by the {@code getunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetunsatassume(Smtlibv2Parser.GetunsatassumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code getunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetunsatcore(Smtlibv2Parser.GetunsatcoreContext ctx);

  /**
   * Visit a parse tree produced by the {@code getval} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetval(Smtlibv2Parser.GetvalContext ctx);

  /**
   * Visit a parse tree produced by the {@code pop} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPop(Smtlibv2Parser.PopContext ctx);

  /**
   * Visit a parse tree produced by the {@code push} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPush(Smtlibv2Parser.PushContext ctx);

  /**
   * Visit a parse tree produced by the {@code reset} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitReset(Smtlibv2Parser.ResetContext ctx);

  /**
   * Visit a parse tree produced by the {@code resetassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResetassert(Smtlibv2Parser.ResetassertContext ctx);

  /**
   * Visit a parse tree produced by the {@code setInfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetInfo(Smtlibv2Parser.SetInfoContext ctx);

  /**
   * Visit a parse tree produced by the {@code setlogic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetlogic(Smtlibv2Parser.SetlogicContext ctx);

  /**
   * Visit a parse tree produced by the {@code setoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetoption(Smtlibv2Parser.SetoptionContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#bvalue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitBvalue(Smtlibv2Parser.BvalueContext ctx);

  /**
   * Visit a parse tree produced by the {@code diagnose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDiagnose(Smtlibv2Parser.DiagnoseContext ctx);

  /**
   * Visit a parse tree produced by the {@code global} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGlobal(Smtlibv2Parser.GlobalContext ctx);

  /**
   * Visit a parse tree produced by the {@code interactive} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInteractive(Smtlibv2Parser.InteractiveContext ctx);

  /**
   * Visit a parse tree produced by the {@code printsucc} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPrintsucc(Smtlibv2Parser.PrintsuccContext ctx);

  /**
   * Visit a parse tree produced by the {@code prodassert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdassert(Smtlibv2Parser.ProdassertContext ctx);

  /**
   * Visit a parse tree produced by the {@code prodassign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdassign(Smtlibv2Parser.ProdassignContext ctx);

  /**
   * Visit a parse tree produced by the {@code prodmod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdmod(Smtlibv2Parser.ProdmodContext ctx);

  /**
   * Visit a parse tree produced by the {@code prodproofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdproofs(Smtlibv2Parser.ProdproofsContext ctx);

  /**
   * Visit a parse tree produced by the {@code produnsatassume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdunsatassume(Smtlibv2Parser.ProdunsatassumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code produnsatcore} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProdunsatcore(Smtlibv2Parser.ProdunsatcoreContext ctx);

  /**
   * Visit a parse tree produced by the {@code randseed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRandseed(Smtlibv2Parser.RandseedContext ctx);

  /**
   * Visit a parse tree produced by the {@code regout} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRegout(Smtlibv2Parser.RegoutContext ctx);

  /**
   * Visit a parse tree produced by the {@code repro} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRepro(Smtlibv2Parser.ReproContext ctx);

  /**
   * Visit a parse tree produced by the {@code verbose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVerbose(Smtlibv2Parser.VerboseContext ctx);

  /**
   * Visit a parse tree produced by the {@code optattr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitOptattr(Smtlibv2Parser.OptattrContext ctx);

  /**
   * Visit a parse tree produced by the {@code allstat} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAllstat(Smtlibv2Parser.AllstatContext ctx);

  /**
   * Visit a parse tree produced by the {@code assertstack} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAssertstack(Smtlibv2Parser.AssertstackContext ctx);

  /**
   * Visit a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Visit a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Visit a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitName(Smtlibv2Parser.NameContext ctx);

  /**
   * Visit a parse tree produced by the {@code runknown} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRunknown(Smtlibv2Parser.RunknownContext ctx);

  /**
   * Visit a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Visit a parse tree produced by the {@code infokey} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfokey(Smtlibv2Parser.InfokeyContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#errorbehaviour}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitErrorbehaviour(Smtlibv2Parser.ErrorbehaviourContext ctx);

  /**
   * Visit a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Visit a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Visit a parse tree produced by the {@code runnownsexpr} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRunnownsexpr(Smtlibv2Parser.RunnownsexprContext ctx);

  /**
   * Visit a parse tree produced by the {@code respdeffun} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespdeffun(Smtlibv2Parser.RespdeffunContext ctx);

  /**
   * Visit a parse tree produced by the {@code respdeffunrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespdeffunrec(Smtlibv2Parser.RespdeffunrecContext ctx);

  /**
   * Visit a parse tree produced by the {@code respdeffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespdeffunsrec(Smtlibv2Parser.RespdeffunsrecContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoassertstack} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoassertstack(Smtlibv2Parser.InfoassertstackContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoauthors} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoauthors(Smtlibv2Parser.InfoauthorsContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoerror} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoerror(Smtlibv2Parser.InfoerrorContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoname} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoname(Smtlibv2Parser.InfonameContext ctx);

  /**
   * Visit a parse tree produced by the {@code inforunknown} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInforunknown(Smtlibv2Parser.InforunknownContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoversion} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoversion(Smtlibv2Parser.InfoversionContext ctx);

  /**
   * Visit a parse tree produced by the {@code infoattr} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfoattr(Smtlibv2Parser.InfoattrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#valuationpair}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitValuationpair(Smtlibv2Parser.ValuationpairContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#tvaluationpair}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTvaluationpair(Smtlibv2Parser.TvaluationpairContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#checksatresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitChecksatresponse(Smtlibv2Parser.ChecksatresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#echoresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitEchoresponse(Smtlibv2Parser.EchoresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getassertionsresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetassertionsresponse(Smtlibv2Parser.GetassertionsresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getassignmentresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetassignmentresponse(Smtlibv2Parser.GetassignmentresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getinforesponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetinforesponse(Smtlibv2Parser.GetinforesponseContext ctx);

  /**
   * Visit a parse tree produced by the {@code rsmodel} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRsmodel(Smtlibv2Parser.RsmodelContext ctx);

  /**
   * Visit a parse tree produced by the {@code modelresp} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitModelresp(Smtlibv2Parser.ModelrespContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getoptionresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetoptionresponse(Smtlibv2Parser.GetoptionresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getproofresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetproofresponse(Smtlibv2Parser.GetproofresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getunsatassumpresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetunsatassumpresponse(Smtlibv2Parser.GetunsatassumpresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getunsatcoreresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetunsatcoreresponse(Smtlibv2Parser.GetunsatcoreresponseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#getvalueresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGetvalueresponse(Smtlibv2Parser.GetvalueresponseContext ctx);

  /**
   * Visit a parse tree produced by the {@code respchecksat} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespchecksat(Smtlibv2Parser.RespchecksatContext ctx);

  /**
   * Visit a parse tree produced by the {@code respecho} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespecho(Smtlibv2Parser.RespechoContext ctx);

  /**
   * Visit a parse tree produced by the {@code respgetassert} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespgetassert(Smtlibv2Parser.RespgetassertContext ctx);

  /**
   * Visit a parse tree produced by the {@code respgettassign} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespgettassign(Smtlibv2Parser.RespgettassignContext ctx);

  /**
   * Visit a parse tree produced by the {@code respgetinfo} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespgetinfo(Smtlibv2Parser.RespgetinfoContext ctx);

  /**
   * Visit a parse tree produced by the {@code respgetmodel} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespgetmodel(Smtlibv2Parser.RespgetmodelContext ctx);

  /**
   * Visit a parse tree produced by the {@code respoption} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespoption(Smtlibv2Parser.RespoptionContext ctx);

  /**
   * Visit a parse tree produced by the {@code respproof} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespproof(Smtlibv2Parser.RespproofContext ctx);

  /**
   * Visit a parse tree produced by the {@code respunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespunsatassume(Smtlibv2Parser.RespunsatassumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code respunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespunsatcore(Smtlibv2Parser.RespunsatcoreContext ctx);

  /**
   * Visit a parse tree produced by the {@code respvalue} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespvalue(Smtlibv2Parser.RespvalueContext ctx);

  /**
   * Visit a parse tree produced by the {@code respsuccess} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespsuccess(Smtlibv2Parser.RespsuccessContext ctx);

  /**
   * Visit a parse tree produced by the {@code respspecsuccesss} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespspecsuccesss(Smtlibv2Parser.RespspecsuccesssContext ctx);

  /**
   * Visit a parse tree produced by the {@code respunsupported} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRespunsupported(Smtlibv2Parser.RespunsupportedContext ctx);

  /**
   * Visit a parse tree produced by the {@code resperror} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResperror(Smtlibv2Parser.ResperrorContext ctx);
}
