// Generated from
// /home/dalux/Dokumente/IdeaProjects/java-smt/src/
// org/sosy_lab/javaSmt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by {@link Smtlibv2Parser}.
 */
public interface Smtlibv2Listener extends ParseTreeListener {
  /**
   * Enter a parse tree produced by the {@code startlogic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStartlogic(Smtlibv2Parser.StartlogicContext ctx);

  /**
   * Exit a parse tree produced by the {@code startlogic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStartlogic(Smtlibv2Parser.StartlogicContext ctx);

  /**
   * Enter a parse tree produced by the {@code starttheory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStarttheory(Smtlibv2Parser.StarttheoryContext ctx);

  /**
   * Exit a parse tree produced by the {@code starttheory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStarttheory(Smtlibv2Parser.StarttheoryContext ctx);

  /**
   * Enter a parse tree produced by the {@code startscript} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStartscript(Smtlibv2Parser.StartscriptContext ctx);

  /**
   * Exit a parse tree produced by the {@code startscript} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStartscript(Smtlibv2Parser.StartscriptContext ctx);

  /**
   * Enter a parse tree produced by the {@code startgenresp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStartgenresp(Smtlibv2Parser.StartgenrespContext ctx);

  /**
   * Exit a parse tree produced by the {@code startgenresp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStartgenresp(Smtlibv2Parser.StartgenrespContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#generalReservedWord}.
   *
   * @param ctx the parse tree
   */
  void enterGeneralReservedWord(Smtlibv2Parser.GeneralReservedWordContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#generalReservedWord}.
   *
   * @param ctx the parse tree
   */
  void exitGeneralReservedWord(Smtlibv2Parser.GeneralReservedWordContext ctx);

  /**
   * Enter a parse tree produced by the {@code simppresymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterSimppresymb(Smtlibv2Parser.SimppresymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code simppresymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitSimppresymb(Smtlibv2Parser.SimppresymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code simpundefsymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterSimpundefsymb(Smtlibv2Parser.SimpundefsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code simpundefsymb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitSimpundefsymb(Smtlibv2Parser.SimpundefsymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#quotedSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterQuotedSymbol(Smtlibv2Parser.QuotedSymbolContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#quotedSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitQuotedSymbol(Smtlibv2Parser.QuotedSymbolContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#predefSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterPredefSymbol(Smtlibv2Parser.PredefSymbolContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#predefSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitPredefSymbol(Smtlibv2Parser.PredefSymbolContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#predefKeyword}.
   *
   * @param ctx the parse tree
   */
  void enterPredefKeyword(Smtlibv2Parser.PredefKeywordContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#predefKeyword}.
   *
   * @param ctx the parse tree
   */
  void exitPredefKeyword(Smtlibv2Parser.PredefKeywordContext ctx);

  /**
   * Enter a parse tree produced by the {@code simpsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   */
  void enterSimpsymb(Smtlibv2Parser.SimpsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code simpsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   */
  void exitSimpsymb(Smtlibv2Parser.SimpsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code quotsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   */
  void enterQuotsymb(Smtlibv2Parser.QuotsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code quotsymb} labeled alternative in {@link
   * Smtlibv2Parser#symbol}.
   *
   * @param ctx the parse tree
   */
  void exitQuotsymb(Smtlibv2Parser.QuotsymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#numeral}.
   *
   * @param ctx the parse tree
   */
  void enterNumeral(Smtlibv2Parser.NumeralContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#numeral}.
   *
   * @param ctx the parse tree
   */
  void exitNumeral(Smtlibv2Parser.NumeralContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#decimal}.
   *
   * @param ctx the parse tree
   */
  void enterDecimal(Smtlibv2Parser.DecimalContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#decimal}.
   *
   * @param ctx the parse tree
   */
  void exitDecimal(Smtlibv2Parser.DecimalContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#hexadecimal}.
   *
   * @param ctx the parse tree
   */
  void enterHexadecimal(Smtlibv2Parser.HexadecimalContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#hexadecimal}.
   *
   * @param ctx the parse tree
   */
  void exitHexadecimal(Smtlibv2Parser.HexadecimalContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#binary}.
   *
   * @param ctx the parse tree
   */
  void enterBinary(Smtlibv2Parser.BinaryContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#binary}.
   *
   * @param ctx the parse tree
   */
  void exitBinary(Smtlibv2Parser.BinaryContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#string}.
   *
   * @param ctx the parse tree
   */
  void enterString(Smtlibv2Parser.StringContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#string}.
   *
   * @param ctx the parse tree
   */
  void exitString(Smtlibv2Parser.StringContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#floatingpoint}.
   *
   * @param ctx the parse tree
   */
  void enterFloatingpoint(Smtlibv2Parser.FloatingpointContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#floatingpoint}.
   *
   * @param ctx the parse tree
   */
  void exitFloatingpoint(Smtlibv2Parser.FloatingpointContext ctx);

  /**
   * Enter a parse tree produced by the {@code prekey} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void enterPrekey(Smtlibv2Parser.PrekeyContext ctx);

  /**
   * Exit a parse tree produced by the {@code prekey} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void exitPrekey(Smtlibv2Parser.PrekeyContext ctx);

  /**
   * Enter a parse tree produced by the {@code keysimsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void enterKeysimsymb(Smtlibv2Parser.KeysimsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code keysimsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void exitKeysimsymb(Smtlibv2Parser.KeysimsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstantnum} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstantnum(Smtlibv2Parser.SpecconstantnumContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstantnum} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstantnum(Smtlibv2Parser.SpecconstantnumContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstantdec} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstantdec(Smtlibv2Parser.SpecconstantdecContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstantdec} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstantdec(Smtlibv2Parser.SpecconstantdecContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstanthex} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstanthex(Smtlibv2Parser.SpecconstanthexContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstanthex} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstanthex(Smtlibv2Parser.SpecconstanthexContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstantbin} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstantbin(Smtlibv2Parser.SpecconstantbinContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstantbin} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstantbin(Smtlibv2Parser.SpecconstantbinContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstantstring} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstantstring(Smtlibv2Parser.SpecconstantstringContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstantstring} labeled alternative in {@link
   * Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstantstring(Smtlibv2Parser.SpecconstantstringContext ctx);

  /**
   * Enter a parse tree produced by the {@code specconstantfloatingpoint} labeled alternative in
   * {@link Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void enterSpecconstantfloatingpoint(Smtlibv2Parser.SpecconstantfloatingpointContext ctx);

  /**
   * Exit a parse tree produced by the {@code specconstantfloatingpoint} labeled alternative in
   * {@link Smtlibv2Parser#specconstant}.
   *
   * @param ctx the parse tree
   */
  void exitSpecconstantfloatingpoint(Smtlibv2Parser.SpecconstantfloatingpointContext ctx);

  /**
   * Enter a parse tree produced by the {@code sexprspec} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void enterSexprspec(Smtlibv2Parser.SexprspecContext ctx);

  /**
   * Exit a parse tree produced by the {@code sexprspec} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void exitSexprspec(Smtlibv2Parser.SexprspecContext ctx);

  /**
   * Enter a parse tree produced by the {@code sexprsymb} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void enterSexprsymb(Smtlibv2Parser.SexprsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code sexprsymb} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void exitSexprsymb(Smtlibv2Parser.SexprsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code sexprkey} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void enterSexprkey(Smtlibv2Parser.SexprkeyContext ctx);

  /**
   * Exit a parse tree produced by the {@code sexprkey} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void exitSexprkey(Smtlibv2Parser.SexprkeyContext ctx);

  /**
   * Enter a parse tree produced by the {@code multisexpr} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void enterMultisexpr(Smtlibv2Parser.MultisexprContext ctx);

  /**
   * Exit a parse tree produced by the {@code multisexpr} labeled alternative in {@link
   * Smtlibv2Parser#sexpr}.
   *
   * @param ctx the parse tree
   */
  void exitMultisexpr(Smtlibv2Parser.MultisexprContext ctx);

  /**
   * Enter a parse tree produced by the {@code idxnum} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void enterIdxnum(Smtlibv2Parser.IdxnumContext ctx);

  /**
   * Exit a parse tree produced by the {@code idxnum} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void exitIdxnum(Smtlibv2Parser.IdxnumContext ctx);

  /**
   * Enter a parse tree produced by the {@code idxsymb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void enterIdxsymb(Smtlibv2Parser.IdxsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code idxsymb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void exitIdxsymb(Smtlibv2Parser.IdxsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code idsymb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void enterIdsymb(Smtlibv2Parser.IdsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code idsymb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void exitIdsymb(Smtlibv2Parser.IdsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code idsymbidx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void enterIdsymbidx(Smtlibv2Parser.IdsymbidxContext ctx);

  /**
   * Exit a parse tree produced by the {@code idsymbidx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void exitIdsymbidx(Smtlibv2Parser.IdsymbidxContext ctx);

  /**
   * Enter a parse tree produced by the {@code attrspec} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void enterAttrspec(Smtlibv2Parser.AttrspecContext ctx);

  /**
   * Exit a parse tree produced by the {@code attrspec} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void exitAttrspec(Smtlibv2Parser.AttrspecContext ctx);

  /**
   * Enter a parse tree produced by the {@code attrsymb} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void enterAttrsymb(Smtlibv2Parser.AttrsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code attrsymb} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void exitAttrsymb(Smtlibv2Parser.AttrsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code attrsexpr} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void enterAttrsexpr(Smtlibv2Parser.AttrsexprContext ctx);

  /**
   * Exit a parse tree produced by the {@code attrsexpr} labeled alternative in {@link
   * Smtlibv2Parser#attributevalue}.
   *
   * @param ctx the parse tree
   */
  void exitAttrsexpr(Smtlibv2Parser.AttrsexprContext ctx);

  /**
   * Enter a parse tree produced by the {@code attrkey} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void enterAttrkey(Smtlibv2Parser.AttrkeyContext ctx);

  /**
   * Exit a parse tree produced by the {@code attrkey} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void exitAttrkey(Smtlibv2Parser.AttrkeyContext ctx);

  /**
   * Enter a parse tree produced by the {@code attrkeyattr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void enterAttrkeyattr(Smtlibv2Parser.AttrkeyattrContext ctx);

  /**
   * Exit a parse tree produced by the {@code attrkeyattr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void exitAttrkeyattr(Smtlibv2Parser.AttrkeyattrContext ctx);

  /**
   * Enter a parse tree produced by the {@code sortid} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void enterSortid(Smtlibv2Parser.SortidContext ctx);

  /**
   * Exit a parse tree produced by the {@code sortid} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void exitSortid(Smtlibv2Parser.SortidContext ctx);

  /**
   * Enter a parse tree produced by the {@code multisort} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void enterMultisort(Smtlibv2Parser.MultisortContext ctx);

  /**
   * Exit a parse tree produced by the {@code multisort} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void exitMultisort(Smtlibv2Parser.MultisortContext ctx);

  /**
   * Enter a parse tree produced by the {@code qualid} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   */
  void enterQualid(Smtlibv2Parser.QualidContext ctx);

  /**
   * Exit a parse tree produced by the {@code qualid} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   */
  void exitQualid(Smtlibv2Parser.QualidContext ctx);

  /**
   * Enter a parse tree produced by the {@code qualidsort} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   */
  void enterQualidsort(Smtlibv2Parser.QualidsortContext ctx);

  /**
   * Exit a parse tree produced by the {@code qualidsort} labeled alternative in {@link
   * Smtlibv2Parser#qualidentifer}.
   *
   * @param ctx the parse tree
   */
  void exitQualidsort(Smtlibv2Parser.QualidsortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#varbinding}.
   *
   * @param ctx the parse tree
   */
  void enterVarbinding(Smtlibv2Parser.VarbindingContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#varbinding}.
   *
   * @param ctx the parse tree
   */
  void exitVarbinding(Smtlibv2Parser.VarbindingContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#sortedvar}.
   *
   * @param ctx the parse tree
   */
  void enterSortedvar(Smtlibv2Parser.SortedvarContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sortedvar}.
   *
   * @param ctx the parse tree
   */
  void exitSortedvar(Smtlibv2Parser.SortedvarContext ctx);

  /**
   * Enter a parse tree produced by the {@code patternsymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void enterPatternsymb(Smtlibv2Parser.PatternsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code patternsymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void exitPatternsymb(Smtlibv2Parser.PatternsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code patternmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void enterPatternmultisymb(Smtlibv2Parser.PatternmultisymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code patternmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void exitPatternmultisymb(Smtlibv2Parser.PatternmultisymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#matchcase}.
   *
   * @param ctx the parse tree
   */
  void enterMatchcase(Smtlibv2Parser.MatchcaseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#matchcase}.
   *
   * @param ctx the parse tree
   */
  void exitMatchcase(Smtlibv2Parser.MatchcaseContext ctx);

  /**
   * Enter a parse tree produced by the {@code termspecconst} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermspecconst(Smtlibv2Parser.TermspecconstContext ctx);

  /**
   * Exit a parse tree produced by the {@code termspecconst} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermspecconst(Smtlibv2Parser.TermspecconstContext ctx);

  /**
   * Enter a parse tree produced by the {@code termqualid} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermqualid(Smtlibv2Parser.TermqualidContext ctx);

  /**
   * Exit a parse tree produced by the {@code termqualid} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermqualid(Smtlibv2Parser.TermqualidContext ctx);

  /**
   * Enter a parse tree produced by the {@code multiterm} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterMultiterm(Smtlibv2Parser.MultitermContext ctx);

  /**
   * Exit a parse tree produced by the {@code multiterm} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitMultiterm(Smtlibv2Parser.MultitermContext ctx);

  /**
   * Enter a parse tree produced by the {@code termlet} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermlet(Smtlibv2Parser.TermletContext ctx);

  /**
   * Exit a parse tree produced by the {@code termlet} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermlet(Smtlibv2Parser.TermletContext ctx);

  /**
   * Enter a parse tree produced by the {@code termforall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermforall(Smtlibv2Parser.TermforallContext ctx);

  /**
   * Exit a parse tree produced by the {@code termforall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermforall(Smtlibv2Parser.TermforallContext ctx);

  /**
   * Enter a parse tree produced by the {@code termexists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermexists(Smtlibv2Parser.TermexistsContext ctx);

  /**
   * Exit a parse tree produced by the {@code termexists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermexists(Smtlibv2Parser.TermexistsContext ctx);

  /**
   * Enter a parse tree produced by the {@code termmatch} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermmatch(Smtlibv2Parser.TermmatchContext ctx);

  /**
   * Exit a parse tree produced by the {@code termmatch} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermmatch(Smtlibv2Parser.TermmatchContext ctx);

  /**
   * Enter a parse tree produced by the {@code termexclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTermexclam(Smtlibv2Parser.TermexclamContext ctx);

  /**
   * Exit a parse tree produced by the {@code termexclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTermexclam(Smtlibv2Parser.TermexclamContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#sortsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterSortsymboldecl(Smtlibv2Parser.SortsymboldeclContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sortsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitSortsymboldecl(Smtlibv2Parser.SortsymboldeclContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#metaspecconstant}.
   *
   * @param ctx the parse tree
   */
  void enterMetaspecconstant(Smtlibv2Parser.MetaspecconstantContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#metaspecconstant}.
   *
   * @param ctx the parse tree
   */
  void exitMetaspecconstant(Smtlibv2Parser.MetaspecconstantContext ctx);

  /**
   * Enter a parse tree produced by the {@code funsymbspec} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterFunsymbspec(Smtlibv2Parser.FunsymbspecContext ctx);

  /**
   * Exit a parse tree produced by the {@code funsymbspec} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitFunsymbspec(Smtlibv2Parser.FunsymbspecContext ctx);

  /**
   * Enter a parse tree produced by the {@code funsymbmeta} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterFunsymbmeta(Smtlibv2Parser.FunsymbmetaContext ctx);

  /**
   * Exit a parse tree produced by the {@code funsymbmeta} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitFunsymbmeta(Smtlibv2Parser.FunsymbmetaContext ctx);

  /**
   * Enter a parse tree produced by the {@code funsymbid} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterFunsymbid(Smtlibv2Parser.FunsymbidContext ctx);

  /**
   * Exit a parse tree produced by the {@code funsymbid} labeled alternative in {@link
   * Smtlibv2Parser#funsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitFunsymbid(Smtlibv2Parser.FunsymbidContext ctx);

  /**
   * Enter a parse tree produced by the {@code parfunsymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterParfunsymb(Smtlibv2Parser.ParfunsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code parfunsymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitParfunsymb(Smtlibv2Parser.ParfunsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code parfunmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void enterParfunmultisymb(Smtlibv2Parser.ParfunmultisymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code parfunmultisymb} labeled alternative in {@link
   * Smtlibv2Parser#parfunsymboldecl}.
   *
   * @param ctx the parse tree
   */
  void exitParfunmultisymb(Smtlibv2Parser.ParfunmultisymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code theorysort} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheorysort(Smtlibv2Parser.TheorysortContext ctx);

  /**
   * Exit a parse tree produced by the {@code theorysort} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheorysort(Smtlibv2Parser.TheorysortContext ctx);

  /**
   * Enter a parse tree produced by the {@code theoryfun} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheoryfun(Smtlibv2Parser.TheoryfunContext ctx);

  /**
   * Exit a parse tree produced by the {@code theoryfun} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheoryfun(Smtlibv2Parser.TheoryfunContext ctx);

  /**
   * Enter a parse tree produced by the {@code theorysortdescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheorysortdescr(Smtlibv2Parser.TheorysortdescrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theorysortdescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheorysortdescr(Smtlibv2Parser.TheorysortdescrContext ctx);

  /**
   * Enter a parse tree produced by the {@code theoryfundescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheoryfundescr(Smtlibv2Parser.TheoryfundescrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theoryfundescr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheoryfundescr(Smtlibv2Parser.TheoryfundescrContext ctx);

  /**
   * Enter a parse tree produced by the {@code theorydef} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheorydef(Smtlibv2Parser.TheorydefContext ctx);

  /**
   * Exit a parse tree produced by the {@code theorydef} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheorydef(Smtlibv2Parser.TheorydefContext ctx);

  /**
   * Enter a parse tree produced by the {@code theoryval} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheoryval(Smtlibv2Parser.TheoryvalContext ctx);

  /**
   * Exit a parse tree produced by the {@code theoryval} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheoryval(Smtlibv2Parser.TheoryvalContext ctx);

  /**
   * Enter a parse tree produced by the {@code theorynotes} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheorynotes(Smtlibv2Parser.TheorynotesContext ctx);

  /**
   * Exit a parse tree produced by the {@code theorynotes} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheorynotes(Smtlibv2Parser.TheorynotesContext ctx);

  /**
   * Enter a parse tree produced by the {@code theoryattr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheoryattr(Smtlibv2Parser.TheoryattrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theoryattr} labeled alternative in {@link
   * Smtlibv2Parser#theoryattribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheoryattr(Smtlibv2Parser.TheoryattrContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#theorydecl}.
   *
   * @param ctx the parse tree
   */
  void enterTheorydecl(Smtlibv2Parser.TheorydeclContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#theorydecl}.
   *
   * @param ctx the parse tree
   */
  void exitTheorydecl(Smtlibv2Parser.TheorydeclContext ctx);

  /**
   * Enter a parse tree produced by the {@code logictheory} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogictheory(Smtlibv2Parser.LogictheoryContext ctx);

  /**
   * Exit a parse tree produced by the {@code logictheory} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogictheory(Smtlibv2Parser.LogictheoryContext ctx);

  /**
   * Enter a parse tree produced by the {@code logiclanguage} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogiclanguage(Smtlibv2Parser.LogiclanguageContext ctx);

  /**
   * Exit a parse tree produced by the {@code logiclanguage} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogiclanguage(Smtlibv2Parser.LogiclanguageContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicext} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogicext(Smtlibv2Parser.LogicextContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicext} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogicext(Smtlibv2Parser.LogicextContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicval} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogicval(Smtlibv2Parser.LogicvalContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicval} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogicval(Smtlibv2Parser.LogicvalContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicnotes} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogicnotes(Smtlibv2Parser.LogicnotesContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicnotes} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogicnotes(Smtlibv2Parser.LogicnotesContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicattr} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogicattr(Smtlibv2Parser.LogicattrContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicattr} labeled alternative in {@link
   * Smtlibv2Parser#logicattribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogicattr(Smtlibv2Parser.LogicattrContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#logic}.
   *
   * @param ctx the parse tree
   */
  void enterLogic(Smtlibv2Parser.LogicContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#logic}.
   *
   * @param ctx the parse tree
   */
  void exitLogic(Smtlibv2Parser.LogicContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#sortdec}.
   *
   * @param ctx the parse tree
   */
  void enterSortdec(Smtlibv2Parser.SortdecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sortdec}.
   *
   * @param ctx the parse tree
   */
  void exitSortdec(Smtlibv2Parser.SortdecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#selectordec}.
   *
   * @param ctx the parse tree
   */
  void enterSelectordec(Smtlibv2Parser.SelectordecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#selectordec}.
   *
   * @param ctx the parse tree
   */
  void exitSelectordec(Smtlibv2Parser.SelectordecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#constructordec}.
   *
   * @param ctx the parse tree
   */
  void enterConstructordec(Smtlibv2Parser.ConstructordecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#constructordec}.
   *
   * @param ctx the parse tree
   */
  void exitConstructordec(Smtlibv2Parser.ConstructordecContext ctx);

  /**
   * Enter a parse tree produced by the {@code dataconstr} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   */
  void enterDataconstr(Smtlibv2Parser.DataconstrContext ctx);

  /**
   * Exit a parse tree produced by the {@code dataconstr} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   */
  void exitDataconstr(Smtlibv2Parser.DataconstrContext ctx);

  /**
   * Enter a parse tree produced by the {@code datamultisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   */
  void enterDatamultisymb(Smtlibv2Parser.DatamultisymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code datamultisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatypedec}.
   *
   * @param ctx the parse tree
   */
  void exitDatamultisymb(Smtlibv2Parser.DatamultisymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#functiondec}.
   *
   * @param ctx the parse tree
   */
  void enterFunctiondec(Smtlibv2Parser.FunctiondecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#functiondec}.
   *
   * @param ctx the parse tree
   */
  void exitFunctiondec(Smtlibv2Parser.FunctiondecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#functiondef}.
   *
   * @param ctx the parse tree
   */
  void enterFunctiondef(Smtlibv2Parser.FunctiondefContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#functiondef}.
   *
   * @param ctx the parse tree
   */
  void exitFunctiondef(Smtlibv2Parser.FunctiondefContext ctx);

  /**
   * Enter a parse tree produced by the {@code propsymb} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   */
  void enterPropsymb(Smtlibv2Parser.PropsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code propsymb} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   */
  void exitPropsymb(Smtlibv2Parser.PropsymbContext ctx);

  /**
   * Enter a parse tree produced by the {@code propnot} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   */
  void enterPropnot(Smtlibv2Parser.PropnotContext ctx);

  /**
   * Exit a parse tree produced by the {@code propnot} labeled alternative in {@link
   * Smtlibv2Parser#propliteral}.
   *
   * @param ctx the parse tree
   */
  void exitPropnot(Smtlibv2Parser.PropnotContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#script}.
   *
   * @param ctx the parse tree
   */
  void enterScript(Smtlibv2Parser.ScriptContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#script}.
   *
   * @param ctx the parse tree
   */
  void exitScript(Smtlibv2Parser.ScriptContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdassert}.
   *
   * @param ctx the parse tree
   */
  void enterCmdassert(Smtlibv2Parser.CmdassertContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdassert}.
   *
   * @param ctx the parse tree
   */
  void exitCmdassert(Smtlibv2Parser.CmdassertContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdcheckSat}.
   *
   * @param ctx the parse tree
   */
  void enterCmdcheckSat(Smtlibv2Parser.CmdcheckSatContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdcheckSat}.
   *
   * @param ctx the parse tree
   */
  void exitCmdcheckSat(Smtlibv2Parser.CmdcheckSatContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdcheckSatAssuming}.
   *
   * @param ctx the parse tree
   */
  void enterCmdcheckSatAssuming(Smtlibv2Parser.CmdcheckSatAssumingContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdcheckSatAssuming}.
   *
   * @param ctx the parse tree
   */
  void exitCmdcheckSatAssuming(Smtlibv2Parser.CmdcheckSatAssumingContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddeclareConst}.
   *
   * @param ctx the parse tree
   */
  void enterCmddeclareConst(Smtlibv2Parser.CmddeclareConstContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddeclareConst}.
   *
   * @param ctx the parse tree
   */
  void exitCmddeclareConst(Smtlibv2Parser.CmddeclareConstContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatype}.
   *
   * @param ctx the parse tree
   */
  void enterCmddeclareDatatype(Smtlibv2Parser.CmddeclareDatatypeContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatype}.
   *
   * @param ctx the parse tree
   */
  void exitCmddeclareDatatype(Smtlibv2Parser.CmddeclareDatatypeContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatypes}.
   *
   * @param ctx the parse tree
   */
  void enterCmddeclareDatatypes(Smtlibv2Parser.CmddeclareDatatypesContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddeclareDatatypes}.
   *
   * @param ctx the parse tree
   */
  void exitCmddeclareDatatypes(Smtlibv2Parser.CmddeclareDatatypesContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddeclareFun}.
   *
   * @param ctx the parse tree
   */
  void enterCmddeclareFun(Smtlibv2Parser.CmddeclareFunContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddeclareFun}.
   *
   * @param ctx the parse tree
   */
  void exitCmddeclareFun(Smtlibv2Parser.CmddeclareFunContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddeclareSort}.
   *
   * @param ctx the parse tree
   */
  void enterCmddeclareSort(Smtlibv2Parser.CmddeclareSortContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddeclareSort}.
   *
   * @param ctx the parse tree
   */
  void exitCmddeclareSort(Smtlibv2Parser.CmddeclareSortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddefineFun}.
   *
   * @param ctx the parse tree
   */
  void enterCmddefineFun(Smtlibv2Parser.CmddefineFunContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddefineFun}.
   *
   * @param ctx the parse tree
   */
  void exitCmddefineFun(Smtlibv2Parser.CmddefineFunContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddefineFunRec}.
   *
   * @param ctx the parse tree
   */
  void enterCmddefineFunRec(Smtlibv2Parser.CmddefineFunRecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddefineFunRec}.
   *
   * @param ctx the parse tree
   */
  void exitCmddefineFunRec(Smtlibv2Parser.CmddefineFunRecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddefineFunsRec}.
   *
   * @param ctx the parse tree
   */
  void enterCmddefineFunsRec(Smtlibv2Parser.CmddefineFunsRecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddefineFunsRec}.
   *
   * @param ctx the parse tree
   */
  void exitCmddefineFunsRec(Smtlibv2Parser.CmddefineFunsRecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmddefineSort}.
   *
   * @param ctx the parse tree
   */
  void enterCmddefineSort(Smtlibv2Parser.CmddefineSortContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmddefineSort}.
   *
   * @param ctx the parse tree
   */
  void exitCmddefineSort(Smtlibv2Parser.CmddefineSortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdecho}.
   *
   * @param ctx the parse tree
   */
  void enterCmdecho(Smtlibv2Parser.CmdechoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdecho}.
   *
   * @param ctx the parse tree
   */
  void exitCmdecho(Smtlibv2Parser.CmdechoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdexit}.
   *
   * @param ctx the parse tree
   */
  void enterCmdexit(Smtlibv2Parser.CmdexitContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdexit}.
   *
   * @param ctx the parse tree
   */
  void exitCmdexit(Smtlibv2Parser.CmdexitContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetAssertions}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetAssertions(Smtlibv2Parser.CmdgetAssertionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetAssertions}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetAssertions(Smtlibv2Parser.CmdgetAssertionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetAssignment}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetAssignment(Smtlibv2Parser.CmdgetAssignmentContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetAssignment}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetAssignment(Smtlibv2Parser.CmdgetAssignmentContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetInfo}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetInfo(Smtlibv2Parser.CmdgetInfoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetInfo}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetInfo(Smtlibv2Parser.CmdgetInfoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetModel}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetModel(Smtlibv2Parser.CmdgetModelContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetModel}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetModel(Smtlibv2Parser.CmdgetModelContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetOption}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetOption(Smtlibv2Parser.CmdgetOptionContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetOption}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetOption(Smtlibv2Parser.CmdgetOptionContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetProof}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetProof(Smtlibv2Parser.CmdgetProofContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetProof}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetProof(Smtlibv2Parser.CmdgetProofContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatAssumptions}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetUnsatAssumptions(Smtlibv2Parser.CmdgetUnsatAssumptionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatAssumptions}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetUnsatAssumptions(Smtlibv2Parser.CmdgetUnsatAssumptionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatCore}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetUnsatCore(Smtlibv2Parser.CmdgetUnsatCoreContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetUnsatCore}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetUnsatCore(Smtlibv2Parser.CmdgetUnsatCoreContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdgetValue}.
   *
   * @param ctx the parse tree
   */
  void enterCmdgetValue(Smtlibv2Parser.CmdgetValueContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdgetValue}.
   *
   * @param ctx the parse tree
   */
  void exitCmdgetValue(Smtlibv2Parser.CmdgetValueContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdpop}.
   *
   * @param ctx the parse tree
   */
  void enterCmdpop(Smtlibv2Parser.CmdpopContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdpop}.
   *
   * @param ctx the parse tree
   */
  void exitCmdpop(Smtlibv2Parser.CmdpopContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdpush}.
   *
   * @param ctx the parse tree
   */
  void enterCmdpush(Smtlibv2Parser.CmdpushContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdpush}.
   *
   * @param ctx the parse tree
   */
  void exitCmdpush(Smtlibv2Parser.CmdpushContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdreset}.
   *
   * @param ctx the parse tree
   */
  void enterCmdreset(Smtlibv2Parser.CmdresetContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdreset}.
   *
   * @param ctx the parse tree
   */
  void exitCmdreset(Smtlibv2Parser.CmdresetContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdresetAssertions}.
   *
   * @param ctx the parse tree
   */
  void enterCmdresetAssertions(Smtlibv2Parser.CmdresetAssertionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdresetAssertions}.
   *
   * @param ctx the parse tree
   */
  void exitCmdresetAssertions(Smtlibv2Parser.CmdresetAssertionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdsetInfo}.
   *
   * @param ctx the parse tree
   */
  void enterCmdsetInfo(Smtlibv2Parser.CmdsetInfoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdsetInfo}.
   *
   * @param ctx the parse tree
   */
  void exitCmdsetInfo(Smtlibv2Parser.CmdsetInfoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdsetLogic}.
   *
   * @param ctx the parse tree
   */
  void enterCmdsetLogic(Smtlibv2Parser.CmdsetLogicContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdsetLogic}.
   *
   * @param ctx the parse tree
   */
  void exitCmdsetLogic(Smtlibv2Parser.CmdsetLogicContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmdsetOption}.
   *
   * @param ctx the parse tree
   */
  void enterCmdsetOption(Smtlibv2Parser.CmdsetOptionContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmdsetOption}.
   *
   * @param ctx the parse tree
   */
  void exitCmdsetOption(Smtlibv2Parser.CmdsetOptionContext ctx);

  /**
   * Enter a parse tree produced by the {@code assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterAssert(Smtlibv2Parser.AssertContext ctx);

  /**
   * Exit a parse tree produced by the {@code assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitAssert(Smtlibv2Parser.AssertContext ctx);

  /**
   * Enter a parse tree produced by the {@code check} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterCheck(Smtlibv2Parser.CheckContext ctx);

  /**
   * Exit a parse tree produced by the {@code check} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitCheck(Smtlibv2Parser.CheckContext ctx);

  /**
   * Enter a parse tree produced by the {@code checkassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterCheckassume(Smtlibv2Parser.CheckassumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code checkassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitCheckassume(Smtlibv2Parser.CheckassumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code declconst} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeclconst(Smtlibv2Parser.DeclconstContext ctx);

  /**
   * Exit a parse tree produced by the {@code declconst} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeclconst(Smtlibv2Parser.DeclconstContext ctx);

  /**
   * Enter a parse tree produced by the {@code decldata} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecldata(Smtlibv2Parser.DecldataContext ctx);

  /**
   * Exit a parse tree produced by the {@code decldata} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecldata(Smtlibv2Parser.DecldataContext ctx);

  /**
   * Enter a parse tree produced by the {@code decldatas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecldatas(Smtlibv2Parser.DecldatasContext ctx);

  /**
   * Exit a parse tree produced by the {@code decldatas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecldatas(Smtlibv2Parser.DecldatasContext ctx);

  /**
   * Enter a parse tree produced by the {@code declfun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeclfun(Smtlibv2Parser.DeclfunContext ctx);

  /**
   * Exit a parse tree produced by the {@code declfun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeclfun(Smtlibv2Parser.DeclfunContext ctx);

  /**
   * Enter a parse tree produced by the {@code declsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeclsort(Smtlibv2Parser.DeclsortContext ctx);

  /**
   * Exit a parse tree produced by the {@code declsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeclsort(Smtlibv2Parser.DeclsortContext ctx);

  /**
   * Enter a parse tree produced by the {@code deffun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeffun(Smtlibv2Parser.DeffunContext ctx);

  /**
   * Exit a parse tree produced by the {@code deffun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeffun(Smtlibv2Parser.DeffunContext ctx);

  /**
   * Enter a parse tree produced by the {@code deffunrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeffunrec(Smtlibv2Parser.DeffunrecContext ctx);

  /**
   * Exit a parse tree produced by the {@code deffunrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeffunrec(Smtlibv2Parser.DeffunrecContext ctx);

  /**
   * Enter a parse tree produced by the {@code deffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDeffunsrec(Smtlibv2Parser.DeffunsrecContext ctx);

  /**
   * Exit a parse tree produced by the {@code deffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDeffunsrec(Smtlibv2Parser.DeffunsrecContext ctx);

  /**
   * Enter a parse tree produced by the {@code defsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDefsort(Smtlibv2Parser.DefsortContext ctx);

  /**
   * Exit a parse tree produced by the {@code defsort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDefsort(Smtlibv2Parser.DefsortContext ctx);

  /**
   * Enter a parse tree produced by the {@code echo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterEcho(Smtlibv2Parser.EchoContext ctx);

  /**
   * Exit a parse tree produced by the {@code echo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitEcho(Smtlibv2Parser.EchoContext ctx);

  /**
   * Enter a parse tree produced by the {@code exit} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterExit(Smtlibv2Parser.ExitContext ctx);

  /**
   * Exit a parse tree produced by the {@code exit} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitExit(Smtlibv2Parser.ExitContext ctx);

  /**
   * Enter a parse tree produced by the {@code getassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetassert(Smtlibv2Parser.GetassertContext ctx);

  /**
   * Exit a parse tree produced by the {@code getassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetassert(Smtlibv2Parser.GetassertContext ctx);

  /**
   * Enter a parse tree produced by the {@code getassign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetassign(Smtlibv2Parser.GetassignContext ctx);

  /**
   * Exit a parse tree produced by the {@code getassign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetassign(Smtlibv2Parser.GetassignContext ctx);

  /**
   * Enter a parse tree produced by the {@code getinfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetinfo(Smtlibv2Parser.GetinfoContext ctx);

  /**
   * Exit a parse tree produced by the {@code getinfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetinfo(Smtlibv2Parser.GetinfoContext ctx);

  /**
   * Enter a parse tree produced by the {@code getmodel} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetmodel(Smtlibv2Parser.GetmodelContext ctx);

  /**
   * Exit a parse tree produced by the {@code getmodel} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetmodel(Smtlibv2Parser.GetmodelContext ctx);

  /**
   * Enter a parse tree produced by the {@code getoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetoption(Smtlibv2Parser.GetoptionContext ctx);

  /**
   * Exit a parse tree produced by the {@code getoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetoption(Smtlibv2Parser.GetoptionContext ctx);

  /**
   * Enter a parse tree produced by the {@code getproof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetproof(Smtlibv2Parser.GetproofContext ctx);

  /**
   * Exit a parse tree produced by the {@code getproof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetproof(Smtlibv2Parser.GetproofContext ctx);

  /**
   * Enter a parse tree produced by the {@code getunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetunsatassume(Smtlibv2Parser.GetunsatassumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code getunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetunsatassume(Smtlibv2Parser.GetunsatassumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code getunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetunsatcore(Smtlibv2Parser.GetunsatcoreContext ctx);

  /**
   * Exit a parse tree produced by the {@code getunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetunsatcore(Smtlibv2Parser.GetunsatcoreContext ctx);

  /**
   * Enter a parse tree produced by the {@code getval} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGetval(Smtlibv2Parser.GetvalContext ctx);

  /**
   * Exit a parse tree produced by the {@code getval} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGetval(Smtlibv2Parser.GetvalContext ctx);

  /**
   * Enter a parse tree produced by the {@code pop} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterPop(Smtlibv2Parser.PopContext ctx);

  /**
   * Exit a parse tree produced by the {@code pop} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitPop(Smtlibv2Parser.PopContext ctx);

  /**
   * Enter a parse tree produced by the {@code push} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterPush(Smtlibv2Parser.PushContext ctx);

  /**
   * Exit a parse tree produced by the {@code push} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitPush(Smtlibv2Parser.PushContext ctx);

  /**
   * Enter a parse tree produced by the {@code reset} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterReset(Smtlibv2Parser.ResetContext ctx);

  /**
   * Exit a parse tree produced by the {@code reset} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitReset(Smtlibv2Parser.ResetContext ctx);

  /**
   * Enter a parse tree produced by the {@code resetassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterResetassert(Smtlibv2Parser.ResetassertContext ctx);

  /**
   * Exit a parse tree produced by the {@code resetassert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitResetassert(Smtlibv2Parser.ResetassertContext ctx);

  /**
   * Enter a parse tree produced by the {@code setInfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterSetInfo(Smtlibv2Parser.SetInfoContext ctx);

  /**
   * Exit a parse tree produced by the {@code setInfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitSetInfo(Smtlibv2Parser.SetInfoContext ctx);

  /**
   * Enter a parse tree produced by the {@code setlogic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterSetlogic(Smtlibv2Parser.SetlogicContext ctx);

  /**
   * Exit a parse tree produced by the {@code setlogic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitSetlogic(Smtlibv2Parser.SetlogicContext ctx);

  /**
   * Enter a parse tree produced by the {@code setoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterSetoption(Smtlibv2Parser.SetoptionContext ctx);

  /**
   * Exit a parse tree produced by the {@code setoption} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitSetoption(Smtlibv2Parser.SetoptionContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#bvalue}.
   *
   * @param ctx the parse tree
   */
  void enterBvalue(Smtlibv2Parser.BvalueContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#bvalue}.
   *
   * @param ctx the parse tree
   */
  void exitBvalue(Smtlibv2Parser.BvalueContext ctx);

  /**
   * Enter a parse tree produced by the {@code diagnose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterDiagnose(Smtlibv2Parser.DiagnoseContext ctx);

  /**
   * Exit a parse tree produced by the {@code diagnose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitDiagnose(Smtlibv2Parser.DiagnoseContext ctx);

  /**
   * Enter a parse tree produced by the {@code global} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterGlobal(Smtlibv2Parser.GlobalContext ctx);

  /**
   * Exit a parse tree produced by the {@code global} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitGlobal(Smtlibv2Parser.GlobalContext ctx);

  /**
   * Enter a parse tree produced by the {@code interactive} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterInteractive(Smtlibv2Parser.InteractiveContext ctx);

  /**
   * Exit a parse tree produced by the {@code interactive} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitInteractive(Smtlibv2Parser.InteractiveContext ctx);

  /**
   * Enter a parse tree produced by the {@code printsucc} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterPrintsucc(Smtlibv2Parser.PrintsuccContext ctx);

  /**
   * Exit a parse tree produced by the {@code printsucc} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitPrintsucc(Smtlibv2Parser.PrintsuccContext ctx);

  /**
   * Enter a parse tree produced by the {@code prodassert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdassert(Smtlibv2Parser.ProdassertContext ctx);

  /**
   * Exit a parse tree produced by the {@code prodassert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdassert(Smtlibv2Parser.ProdassertContext ctx);

  /**
   * Enter a parse tree produced by the {@code prodassign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdassign(Smtlibv2Parser.ProdassignContext ctx);

  /**
   * Exit a parse tree produced by the {@code prodassign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdassign(Smtlibv2Parser.ProdassignContext ctx);

  /**
   * Enter a parse tree produced by the {@code prodmod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdmod(Smtlibv2Parser.ProdmodContext ctx);

  /**
   * Exit a parse tree produced by the {@code prodmod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdmod(Smtlibv2Parser.ProdmodContext ctx);

  /**
   * Enter a parse tree produced by the {@code prodproofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdproofs(Smtlibv2Parser.ProdproofsContext ctx);

  /**
   * Exit a parse tree produced by the {@code prodproofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdproofs(Smtlibv2Parser.ProdproofsContext ctx);

  /**
   * Enter a parse tree produced by the {@code produnsatassume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdunsatassume(Smtlibv2Parser.ProdunsatassumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code produnsatassume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdunsatassume(Smtlibv2Parser.ProdunsatassumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code produnsatcore} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProdunsatcore(Smtlibv2Parser.ProdunsatcoreContext ctx);

  /**
   * Exit a parse tree produced by the {@code produnsatcore} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProdunsatcore(Smtlibv2Parser.ProdunsatcoreContext ctx);

  /**
   * Enter a parse tree produced by the {@code randseed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterRandseed(Smtlibv2Parser.RandseedContext ctx);

  /**
   * Exit a parse tree produced by the {@code randseed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitRandseed(Smtlibv2Parser.RandseedContext ctx);

  /**
   * Enter a parse tree produced by the {@code regout} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterRegout(Smtlibv2Parser.RegoutContext ctx);

  /**
   * Exit a parse tree produced by the {@code regout} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitRegout(Smtlibv2Parser.RegoutContext ctx);

  /**
   * Enter a parse tree produced by the {@code repro} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterRepro(Smtlibv2Parser.ReproContext ctx);

  /**
   * Exit a parse tree produced by the {@code repro} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitRepro(Smtlibv2Parser.ReproContext ctx);

  /**
   * Enter a parse tree produced by the {@code verbose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterVerbose(Smtlibv2Parser.VerboseContext ctx);

  /**
   * Exit a parse tree produced by the {@code verbose} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitVerbose(Smtlibv2Parser.VerboseContext ctx);

  /**
   * Enter a parse tree produced by the {@code optattr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterOptattr(Smtlibv2Parser.OptattrContext ctx);

  /**
   * Exit a parse tree produced by the {@code optattr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitOptattr(Smtlibv2Parser.OptattrContext ctx);

  /**
   * Enter a parse tree produced by the {@code allstat} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterAllstat(Smtlibv2Parser.AllstatContext ctx);

  /**
   * Exit a parse tree produced by the {@code allstat} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitAllstat(Smtlibv2Parser.AllstatContext ctx);

  /**
   * Enter a parse tree produced by the {@code assertstack} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterAssertstack(Smtlibv2Parser.AssertstackContext ctx);

  /**
   * Exit a parse tree produced by the {@code assertstack} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitAssertstack(Smtlibv2Parser.AssertstackContext ctx);

  /**
   * Enter a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Exit a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Enter a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Exit a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Enter a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterName(Smtlibv2Parser.NameContext ctx);

  /**
   * Exit a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitName(Smtlibv2Parser.NameContext ctx);

  /**
   * Enter a parse tree produced by the {@code runknown} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterRunknown(Smtlibv2Parser.RunknownContext ctx);

  /**
   * Exit a parse tree produced by the {@code runknown} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitRunknown(Smtlibv2Parser.RunknownContext ctx);

  /**
   * Enter a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Exit a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Enter a parse tree produced by the {@code infokey} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void enterInfokey(Smtlibv2Parser.InfokeyContext ctx);

  /**
   * Exit a parse tree produced by the {@code infokey} labeled alternative in {@link
   * Smtlibv2Parser#infoflag}.
   *
   * @param ctx the parse tree
   */
  void exitInfokey(Smtlibv2Parser.InfokeyContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#errorbehaviour}.
   *
   * @param ctx the parse tree
   */
  void enterErrorbehaviour(Smtlibv2Parser.ErrorbehaviourContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#errorbehaviour}.
   *
   * @param ctx the parse tree
   */
  void exitErrorbehaviour(Smtlibv2Parser.ErrorbehaviourContext ctx);

  /**
   * Enter a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void enterMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Exit a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void exitMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Enter a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void enterIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Exit a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void exitIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Enter a parse tree produced by the {@code runnownsexpr} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void enterRunnownsexpr(Smtlibv2Parser.RunnownsexprContext ctx);

  /**
   * Exit a parse tree produced by the {@code runnownsexpr} labeled alternative in {@link
   * Smtlibv2Parser#reasonunknown}.
   *
   * @param ctx the parse tree
   */
  void exitRunnownsexpr(Smtlibv2Parser.RunnownsexprContext ctx);

  /**
   * Enter a parse tree produced by the {@code respdeffun} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespdeffun(Smtlibv2Parser.RespdeffunContext ctx);

  /**
   * Exit a parse tree produced by the {@code respdeffun} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespdeffun(Smtlibv2Parser.RespdeffunContext ctx);

  /**
   * Enter a parse tree produced by the {@code respdeffunrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespdeffunrec(Smtlibv2Parser.RespdeffunrecContext ctx);

  /**
   * Exit a parse tree produced by the {@code respdeffunrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespdeffunrec(Smtlibv2Parser.RespdeffunrecContext ctx);

  /**
   * Enter a parse tree produced by the {@code respdeffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespdeffunsrec(Smtlibv2Parser.RespdeffunsrecContext ctx);

  /**
   * Exit a parse tree produced by the {@code respdeffunsrec} labeled alternative in {@link
   * Smtlibv2Parser#modelresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespdeffunsrec(Smtlibv2Parser.RespdeffunsrecContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoassertstack} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoassertstack(Smtlibv2Parser.InfoassertstackContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoassertstack} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoassertstack(Smtlibv2Parser.InfoassertstackContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoauthors} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoauthors(Smtlibv2Parser.InfoauthorsContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoauthors} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoauthors(Smtlibv2Parser.InfoauthorsContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoerror} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoerror(Smtlibv2Parser.InfoerrorContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoerror} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoerror(Smtlibv2Parser.InfoerrorContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoname} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoname(Smtlibv2Parser.InfonameContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoname} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoname(Smtlibv2Parser.InfonameContext ctx);

  /**
   * Enter a parse tree produced by the {@code inforunknown} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInforunknown(Smtlibv2Parser.InforunknownContext ctx);

  /**
   * Exit a parse tree produced by the {@code inforunknown} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInforunknown(Smtlibv2Parser.InforunknownContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoversion} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoversion(Smtlibv2Parser.InfoversionContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoversion} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoversion(Smtlibv2Parser.InfoversionContext ctx);

  /**
   * Enter a parse tree produced by the {@code infoattr} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterInfoattr(Smtlibv2Parser.InfoattrContext ctx);

  /**
   * Exit a parse tree produced by the {@code infoattr} labeled alternative in {@link
   * Smtlibv2Parser#inforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitInfoattr(Smtlibv2Parser.InfoattrContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#valuationpair}.
   *
   * @param ctx the parse tree
   */
  void enterValuationpair(Smtlibv2Parser.ValuationpairContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#valuationpair}.
   *
   * @param ctx the parse tree
   */
  void exitValuationpair(Smtlibv2Parser.ValuationpairContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#tvaluationpair}.
   *
   * @param ctx the parse tree
   */
  void enterTvaluationpair(Smtlibv2Parser.TvaluationpairContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#tvaluationpair}.
   *
   * @param ctx the parse tree
   */
  void exitTvaluationpair(Smtlibv2Parser.TvaluationpairContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#checksatresponse}.
   *
   * @param ctx the parse tree
   */
  void enterChecksatresponse(Smtlibv2Parser.ChecksatresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#checksatresponse}.
   *
   * @param ctx the parse tree
   */
  void exitChecksatresponse(Smtlibv2Parser.ChecksatresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#echoresponse}.
   *
   * @param ctx the parse tree
   */
  void enterEchoresponse(Smtlibv2Parser.EchoresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#echoresponse}.
   *
   * @param ctx the parse tree
   */
  void exitEchoresponse(Smtlibv2Parser.EchoresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getassertionsresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetassertionsresponse(Smtlibv2Parser.GetassertionsresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getassertionsresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetassertionsresponse(Smtlibv2Parser.GetassertionsresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getassignmentresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetassignmentresponse(Smtlibv2Parser.GetassignmentresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getassignmentresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetassignmentresponse(Smtlibv2Parser.GetassignmentresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getinforesponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetinforesponse(Smtlibv2Parser.GetinforesponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getinforesponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetinforesponse(Smtlibv2Parser.GetinforesponseContext ctx);

  /**
   * Enter a parse tree produced by the {@code rsmodel} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRsmodel(Smtlibv2Parser.RsmodelContext ctx);

  /**
   * Exit a parse tree produced by the {@code rsmodel} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRsmodel(Smtlibv2Parser.RsmodelContext ctx);

  /**
   * Enter a parse tree produced by the {@code modelresp} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   */
  void enterModelresp(Smtlibv2Parser.ModelrespContext ctx);

  /**
   * Exit a parse tree produced by the {@code modelresp} labeled alternative in {@link
   * Smtlibv2Parser#getmodelresponse}.
   *
   * @param ctx the parse tree
   */
  void exitModelresp(Smtlibv2Parser.ModelrespContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getoptionresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetoptionresponse(Smtlibv2Parser.GetoptionresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getoptionresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetoptionresponse(Smtlibv2Parser.GetoptionresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getproofresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetproofresponse(Smtlibv2Parser.GetproofresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getproofresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetproofresponse(Smtlibv2Parser.GetproofresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getunsatassumpresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetunsatassumpresponse(Smtlibv2Parser.GetunsatassumpresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getunsatassumpresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetunsatassumpresponse(Smtlibv2Parser.GetunsatassumpresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getunsatcoreresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetunsatcoreresponse(Smtlibv2Parser.GetunsatcoreresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getunsatcoreresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetunsatcoreresponse(Smtlibv2Parser.GetunsatcoreresponseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#getvalueresponse}.
   *
   * @param ctx the parse tree
   */
  void enterGetvalueresponse(Smtlibv2Parser.GetvalueresponseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#getvalueresponse}.
   *
   * @param ctx the parse tree
   */
  void exitGetvalueresponse(Smtlibv2Parser.GetvalueresponseContext ctx);

  /**
   * Enter a parse tree produced by the {@code respchecksat} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespchecksat(Smtlibv2Parser.RespchecksatContext ctx);

  /**
   * Exit a parse tree produced by the {@code respchecksat} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespchecksat(Smtlibv2Parser.RespchecksatContext ctx);

  /**
   * Enter a parse tree produced by the {@code respecho} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespecho(Smtlibv2Parser.RespechoContext ctx);

  /**
   * Exit a parse tree produced by the {@code respecho} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespecho(Smtlibv2Parser.RespechoContext ctx);

  /**
   * Enter a parse tree produced by the {@code respgetassert} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespgetassert(Smtlibv2Parser.RespgetassertContext ctx);

  /**
   * Exit a parse tree produced by the {@code respgetassert} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespgetassert(Smtlibv2Parser.RespgetassertContext ctx);

  /**
   * Enter a parse tree produced by the {@code respgettassign} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespgettassign(Smtlibv2Parser.RespgettassignContext ctx);

  /**
   * Exit a parse tree produced by the {@code respgettassign} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespgettassign(Smtlibv2Parser.RespgettassignContext ctx);

  /**
   * Enter a parse tree produced by the {@code respgetinfo} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespgetinfo(Smtlibv2Parser.RespgetinfoContext ctx);

  /**
   * Exit a parse tree produced by the {@code respgetinfo} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespgetinfo(Smtlibv2Parser.RespgetinfoContext ctx);

  /**
   * Enter a parse tree produced by the {@code respgetmodel} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespgetmodel(Smtlibv2Parser.RespgetmodelContext ctx);

  /**
   * Exit a parse tree produced by the {@code respgetmodel} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespgetmodel(Smtlibv2Parser.RespgetmodelContext ctx);

  /**
   * Enter a parse tree produced by the {@code respoption} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespoption(Smtlibv2Parser.RespoptionContext ctx);

  /**
   * Exit a parse tree produced by the {@code respoption} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespoption(Smtlibv2Parser.RespoptionContext ctx);

  /**
   * Enter a parse tree produced by the {@code respproof} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespproof(Smtlibv2Parser.RespproofContext ctx);

  /**
   * Exit a parse tree produced by the {@code respproof} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespproof(Smtlibv2Parser.RespproofContext ctx);

  /**
   * Enter a parse tree produced by the {@code respunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespunsatassume(Smtlibv2Parser.RespunsatassumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code respunsatassume} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespunsatassume(Smtlibv2Parser.RespunsatassumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code respunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespunsatcore(Smtlibv2Parser.RespunsatcoreContext ctx);

  /**
   * Exit a parse tree produced by the {@code respunsatcore} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespunsatcore(Smtlibv2Parser.RespunsatcoreContext ctx);

  /**
   * Enter a parse tree produced by the {@code respvalue} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespvalue(Smtlibv2Parser.RespvalueContext ctx);

  /**
   * Exit a parse tree produced by the {@code respvalue} labeled alternative in {@link
   * Smtlibv2Parser#specificsuccessresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespvalue(Smtlibv2Parser.RespvalueContext ctx);

  /**
   * Enter a parse tree produced by the {@code respsuccess} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespsuccess(Smtlibv2Parser.RespsuccessContext ctx);

  /**
   * Exit a parse tree produced by the {@code respsuccess} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespsuccess(Smtlibv2Parser.RespsuccessContext ctx);

  /**
   * Enter a parse tree produced by the {@code respspecsuccesss} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespspecsuccesss(Smtlibv2Parser.RespspecsuccesssContext ctx);

  /**
   * Exit a parse tree produced by the {@code respspecsuccesss} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespspecsuccesss(Smtlibv2Parser.RespspecsuccesssContext ctx);

  /**
   * Enter a parse tree produced by the {@code respunsupported} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void enterRespunsupported(Smtlibv2Parser.RespunsupportedContext ctx);

  /**
   * Exit a parse tree produced by the {@code respunsupported} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void exitRespunsupported(Smtlibv2Parser.RespunsupportedContext ctx);

  /**
   * Enter a parse tree produced by the {@code resperror} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void enterResperror(Smtlibv2Parser.ResperrorContext ctx);

  /**
   * Exit a parse tree produced by the {@code resperror} labeled alternative in {@link
   * Smtlibv2Parser#generalresponse}.
   *
   * @param ctx the parse tree
   */
  void exitResperror(Smtlibv2Parser.ResperrorContext ctx);
}
