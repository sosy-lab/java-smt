// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

// Generated from
// /home/davidg/IdeaProjects/java-smt-working-branch/java-smt/src/org/sosy_lab/java_smt/basicimpl/parserInterpreter/Smtlibv2.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by {@link Smtlibv2Parser}.
 */
public interface Smtlibv2Listener extends ParseTreeListener {
  /**
   * Enter a parse tree produced by the {@code start_logic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStart_logic(Smtlibv2Parser.Start_logicContext ctx);

  /**
   * Exit a parse tree produced by the {@code start_logic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStart_logic(Smtlibv2Parser.Start_logicContext ctx);

  /**
   * Enter a parse tree produced by the {@code start_theory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStart_theory(Smtlibv2Parser.Start_theoryContext ctx);

  /**
   * Exit a parse tree produced by the {@code start_theory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStart_theory(Smtlibv2Parser.Start_theoryContext ctx);

  /**
   * Enter a parse tree produced by the {@code start_script} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStart_script(Smtlibv2Parser.Start_scriptContext ctx);

  /**
   * Exit a parse tree produced by the {@code start_script} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStart_script(Smtlibv2Parser.Start_scriptContext ctx);

  /**
   * Enter a parse tree produced by the {@code start_gen_resp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void enterStart_gen_resp(Smtlibv2Parser.Start_gen_respContext ctx);

  /**
   * Exit a parse tree produced by the {@code start_gen_resp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   */
  void exitStart_gen_resp(Smtlibv2Parser.Start_gen_respContext ctx);

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
   * Enter a parse tree produced by the {@code simp_pre_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterSimp_pre_symb(Smtlibv2Parser.Simp_pre_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code simp_pre_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitSimp_pre_symb(Smtlibv2Parser.Simp_pre_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code simp_undef_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void enterSimp_undef_symb(Smtlibv2Parser.Simp_undef_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code simp_undef_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   */
  void exitSimp_undef_symb(Smtlibv2Parser.Simp_undef_symbContext ctx);

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
   * Enter a parse tree produced by {@link Smtlibv2Parser#to_fp_expr}.
   *
   * @param ctx the parse tree
   */
  void enterTo_fp_expr(Smtlibv2Parser.To_fp_exprContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#to_fp_expr}.
   *
   * @param ctx the parse tree
   */
  void exitTo_fp_expr(Smtlibv2Parser.To_fp_exprContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#special_regex_operations}.
   *
   * @param ctx the parse tree
   */
  void enterSpecial_regex_operations(Smtlibv2Parser.Special_regex_operationsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#special_regex_operations}.
   *
   * @param ctx the parse tree
   */
  void exitSpecial_regex_operations(Smtlibv2Parser.Special_regex_operationsContext ctx);

  /**
   * Enter a parse tree produced by the {@code pre_key} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void enterPre_key(Smtlibv2Parser.Pre_keyContext ctx);

  /**
   * Exit a parse tree produced by the {@code pre_key} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void exitPre_key(Smtlibv2Parser.Pre_keyContext ctx);

  /**
   * Enter a parse tree produced by the {@code key_simsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void enterKey_simsymb(Smtlibv2Parser.Key_simsymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code key_simsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   */
  void exitKey_simsymb(Smtlibv2Parser.Key_simsymbContext ctx);

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
   * Enter a parse tree produced by the {@code spec_constant_num} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_num(Smtlibv2Parser.Spec_constant_numContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_num} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_num(Smtlibv2Parser.Spec_constant_numContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_dec} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_dec(Smtlibv2Parser.Spec_constant_decContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_dec} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_dec(Smtlibv2Parser.Spec_constant_decContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_hex} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_hex(Smtlibv2Parser.Spec_constant_hexContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_hex} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_hex(Smtlibv2Parser.Spec_constant_hexContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_bin} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_bin(Smtlibv2Parser.Spec_constant_binContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_bin} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_bin(Smtlibv2Parser.Spec_constant_binContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_string} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_string(Smtlibv2Parser.Spec_constant_stringContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_string} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_string(Smtlibv2Parser.Spec_constant_stringContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_fp} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_fp(Smtlibv2Parser.Spec_constant_fpContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_fp} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_fp(Smtlibv2Parser.Spec_constant_fpContext ctx);

  /**
   * Enter a parse tree produced by the {@code spec_constant_regex} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterSpec_constant_regex(Smtlibv2Parser.Spec_constant_regexContext ctx);

  /**
   * Exit a parse tree produced by the {@code spec_constant_regex} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitSpec_constant_regex(Smtlibv2Parser.Spec_constant_regexContext ctx);

  /**
   * Enter a parse tree produced by the {@code s_expr_spec} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void enterS_expr_spec(Smtlibv2Parser.S_expr_specContext ctx);

  /**
   * Exit a parse tree produced by the {@code s_expr_spec} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void exitS_expr_spec(Smtlibv2Parser.S_expr_specContext ctx);

  /**
   * Enter a parse tree produced by the {@code s_expr_symb} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void enterS_expr_symb(Smtlibv2Parser.S_expr_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code s_expr_symb} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void exitS_expr_symb(Smtlibv2Parser.S_expr_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code s_expr_key} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void enterS_expr_key(Smtlibv2Parser.S_expr_keyContext ctx);

  /**
   * Exit a parse tree produced by the {@code s_expr_key} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void exitS_expr_key(Smtlibv2Parser.S_expr_keyContext ctx);

  /**
   * Enter a parse tree produced by the {@code multi_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void enterMulti_s_expr(Smtlibv2Parser.Multi_s_exprContext ctx);

  /**
   * Exit a parse tree produced by the {@code multi_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   */
  void exitMulti_s_expr(Smtlibv2Parser.Multi_s_exprContext ctx);

  /**
   * Enter a parse tree produced by the {@code idx_num} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void enterIdx_num(Smtlibv2Parser.Idx_numContext ctx);

  /**
   * Exit a parse tree produced by the {@code idx_num} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void exitIdx_num(Smtlibv2Parser.Idx_numContext ctx);

  /**
   * Enter a parse tree produced by the {@code idx_symb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void enterIdx_symb(Smtlibv2Parser.Idx_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code idx_symb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   */
  void exitIdx_symb(Smtlibv2Parser.Idx_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code id_symb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void enterId_symb(Smtlibv2Parser.Id_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code id_symb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void exitId_symb(Smtlibv2Parser.Id_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code id_symb_idx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void enterId_symb_idx(Smtlibv2Parser.Id_symb_idxContext ctx);

  /**
   * Exit a parse tree produced by the {@code id_symb_idx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   */
  void exitId_symb_idx(Smtlibv2Parser.Id_symb_idxContext ctx);

  /**
   * Enter a parse tree produced by the {@code attr_spec} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void enterAttr_spec(Smtlibv2Parser.Attr_specContext ctx);

  /**
   * Exit a parse tree produced by the {@code attr_spec} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void exitAttr_spec(Smtlibv2Parser.Attr_specContext ctx);

  /**
   * Enter a parse tree produced by the {@code attr_symb} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void enterAttr_symb(Smtlibv2Parser.Attr_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code attr_symb} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void exitAttr_symb(Smtlibv2Parser.Attr_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code attr_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void enterAttr_s_expr(Smtlibv2Parser.Attr_s_exprContext ctx);

  /**
   * Exit a parse tree produced by the {@code attr_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   */
  void exitAttr_s_expr(Smtlibv2Parser.Attr_s_exprContext ctx);

  /**
   * Enter a parse tree produced by the {@code attr_key} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void enterAttr_key(Smtlibv2Parser.Attr_keyContext ctx);

  /**
   * Exit a parse tree produced by the {@code attr_key} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void exitAttr_key(Smtlibv2Parser.Attr_keyContext ctx);

  /**
   * Enter a parse tree produced by the {@code attr_key_attr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void enterAttr_key_attr(Smtlibv2Parser.Attr_key_attrContext ctx);

  /**
   * Exit a parse tree produced by the {@code attr_key_attr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   */
  void exitAttr_key_attr(Smtlibv2Parser.Attr_key_attrContext ctx);

  /**
   * Enter a parse tree produced by the {@code sortfp} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void enterSortfp(Smtlibv2Parser.SortfpContext ctx);

  /**
   * Exit a parse tree produced by the {@code sortfp} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void exitSortfp(Smtlibv2Parser.SortfpContext ctx);

  /**
   * Enter a parse tree produced by the {@code sort_id} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void enterSort_id(Smtlibv2Parser.Sort_idContext ctx);

  /**
   * Exit a parse tree produced by the {@code sort_id} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   */
  void exitSort_id(Smtlibv2Parser.Sort_idContext ctx);

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
   * Enter a parse tree produced by the {@code qual_id} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   */
  void enterQual_id(Smtlibv2Parser.Qual_idContext ctx);

  /**
   * Exit a parse tree produced by the {@code qual_id} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   */
  void exitQual_id(Smtlibv2Parser.Qual_idContext ctx);

  /**
   * Enter a parse tree produced by the {@code qual_id_sort} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   */
  void enterQual_id_sort(Smtlibv2Parser.Qual_id_sortContext ctx);

  /**
   * Exit a parse tree produced by the {@code qual_id_sort} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   */
  void exitQual_id_sort(Smtlibv2Parser.Qual_id_sortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#var_binding}.
   *
   * @param ctx the parse tree
   */
  void enterVar_binding(Smtlibv2Parser.Var_bindingContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#var_binding}.
   *
   * @param ctx the parse tree
   */
  void exitVar_binding(Smtlibv2Parser.Var_bindingContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#sorted_var}.
   *
   * @param ctx the parse tree
   */
  void enterSorted_var(Smtlibv2Parser.Sorted_varContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sorted_var}.
   *
   * @param ctx the parse tree
   */
  void exitSorted_var(Smtlibv2Parser.Sorted_varContext ctx);

  /**
   * Enter a parse tree produced by the {@code pattern_symb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void enterPattern_symb(Smtlibv2Parser.Pattern_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code pattern_symb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void exitPattern_symb(Smtlibv2Parser.Pattern_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code pattern_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void enterPattern_multisymb(Smtlibv2Parser.Pattern_multisymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code pattern_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   */
  void exitPattern_multisymb(Smtlibv2Parser.Pattern_multisymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#match_case}.
   *
   * @param ctx the parse tree
   */
  void enterMatch_case(Smtlibv2Parser.Match_caseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#match_case}.
   *
   * @param ctx the parse tree
   */
  void exitMatch_case(Smtlibv2Parser.Match_caseContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_spec_const} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_spec_const(Smtlibv2Parser.Term_spec_constContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_spec_const} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_spec_const(Smtlibv2Parser.Term_spec_constContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_qual_id} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_qual_id(Smtlibv2Parser.Term_qual_idContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_qual_id} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_qual_id(Smtlibv2Parser.Term_qual_idContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_fp_cast} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_fp_cast(Smtlibv2Parser.Term_fp_castContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_fp_cast} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_fp_cast(Smtlibv2Parser.Term_fp_castContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_special_regex} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_special_regex(Smtlibv2Parser.Term_special_regexContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_special_regex} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_special_regex(Smtlibv2Parser.Term_special_regexContext ctx);

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
   * Enter a parse tree produced by the {@code term_let} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_let(Smtlibv2Parser.Term_letContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_let} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_let(Smtlibv2Parser.Term_letContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_forall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_forall(Smtlibv2Parser.Term_forallContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_forall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_forall(Smtlibv2Parser.Term_forallContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_exists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_exists(Smtlibv2Parser.Term_existsContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_exists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_exists(Smtlibv2Parser.Term_existsContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_match} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_match(Smtlibv2Parser.Term_matchContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_match} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_match(Smtlibv2Parser.Term_matchContext ctx);

  /**
   * Enter a parse tree produced by the {@code term_exclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void enterTerm_exclam(Smtlibv2Parser.Term_exclamContext ctx);

  /**
   * Exit a parse tree produced by the {@code term_exclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   */
  void exitTerm_exclam(Smtlibv2Parser.Term_exclamContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#sort_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterSort_symbol_decl(Smtlibv2Parser.Sort_symbol_declContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sort_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitSort_symbol_decl(Smtlibv2Parser.Sort_symbol_declContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#meta_spec_constant}.
   *
   * @param ctx the parse tree
   */
  void enterMeta_spec_constant(Smtlibv2Parser.Meta_spec_constantContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#meta_spec_constant}.
   *
   * @param ctx the parse tree
   */
  void exitMeta_spec_constant(Smtlibv2Parser.Meta_spec_constantContext ctx);

  /**
   * Enter a parse tree produced by the {@code fun_symb_spec} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterFun_symb_spec(Smtlibv2Parser.Fun_symb_specContext ctx);

  /**
   * Exit a parse tree produced by the {@code fun_symb_spec} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitFun_symb_spec(Smtlibv2Parser.Fun_symb_specContext ctx);

  /**
   * Enter a parse tree produced by the {@code fun_symb_meta} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterFun_symb_meta(Smtlibv2Parser.Fun_symb_metaContext ctx);

  /**
   * Exit a parse tree produced by the {@code fun_symb_meta} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitFun_symb_meta(Smtlibv2Parser.Fun_symb_metaContext ctx);

  /**
   * Enter a parse tree produced by the {@code fun_symb_id} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterFun_symb_id(Smtlibv2Parser.Fun_symb_idContext ctx);

  /**
   * Exit a parse tree produced by the {@code fun_symb_id} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitFun_symb_id(Smtlibv2Parser.Fun_symb_idContext ctx);

  /**
   * Enter a parse tree produced by the {@code par_fun_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterPar_fun_symb(Smtlibv2Parser.Par_fun_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code par_fun_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitPar_fun_symb(Smtlibv2Parser.Par_fun_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code par_fun_multi_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void enterPar_fun_multi_symb(Smtlibv2Parser.Par_fun_multi_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code par_fun_multi_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   */
  void exitPar_fun_multi_symb(Smtlibv2Parser.Par_fun_multi_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_sort} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_sort(Smtlibv2Parser.Theory_sortContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_sort} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_sort(Smtlibv2Parser.Theory_sortContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_fun} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_fun(Smtlibv2Parser.Theory_funContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_fun} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_fun(Smtlibv2Parser.Theory_funContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_sort_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_sort_descr(Smtlibv2Parser.Theory_sort_descrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_sort_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_sort_descr(Smtlibv2Parser.Theory_sort_descrContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_fun_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_fun_descr(Smtlibv2Parser.Theory_fun_descrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_fun_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_fun_descr(Smtlibv2Parser.Theory_fun_descrContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_def} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_def(Smtlibv2Parser.Theory_defContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_def} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_def(Smtlibv2Parser.Theory_defContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_val} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_val(Smtlibv2Parser.Theory_valContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_val} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_val(Smtlibv2Parser.Theory_valContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_notes} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_notes(Smtlibv2Parser.Theory_notesContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_notes} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_notes(Smtlibv2Parser.Theory_notesContext ctx);

  /**
   * Enter a parse tree produced by the {@code theory_attr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_attr(Smtlibv2Parser.Theory_attrContext ctx);

  /**
   * Exit a parse tree produced by the {@code theory_attr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_attr(Smtlibv2Parser.Theory_attrContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#theory_decl}.
   *
   * @param ctx the parse tree
   */
  void enterTheory_decl(Smtlibv2Parser.Theory_declContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#theory_decl}.
   *
   * @param ctx the parse tree
   */
  void exitTheory_decl(Smtlibv2Parser.Theory_declContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_theory} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_theory(Smtlibv2Parser.Logic_theoryContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_theory} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_theory(Smtlibv2Parser.Logic_theoryContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_language} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_language(Smtlibv2Parser.Logic_languageContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_language} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_language(Smtlibv2Parser.Logic_languageContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_ext} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_ext(Smtlibv2Parser.Logic_extContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_ext} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_ext(Smtlibv2Parser.Logic_extContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_val} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_val(Smtlibv2Parser.Logic_valContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_val} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_val(Smtlibv2Parser.Logic_valContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_notes} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_notes(Smtlibv2Parser.Logic_notesContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_notes} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_notes(Smtlibv2Parser.Logic_notesContext ctx);

  /**
   * Enter a parse tree produced by the {@code logic_attr} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void enterLogic_attr(Smtlibv2Parser.Logic_attrContext ctx);

  /**
   * Exit a parse tree produced by the {@code logic_attr} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   */
  void exitLogic_attr(Smtlibv2Parser.Logic_attrContext ctx);

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
   * Enter a parse tree produced by {@link Smtlibv2Parser#sort_dec}.
   *
   * @param ctx the parse tree
   */
  void enterSort_dec(Smtlibv2Parser.Sort_decContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#sort_dec}.
   *
   * @param ctx the parse tree
   */
  void exitSort_dec(Smtlibv2Parser.Sort_decContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#selector_dec}.
   *
   * @param ctx the parse tree
   */
  void enterSelector_dec(Smtlibv2Parser.Selector_decContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#selector_dec}.
   *
   * @param ctx the parse tree
   */
  void exitSelector_dec(Smtlibv2Parser.Selector_decContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#constructor_dec}.
   *
   * @param ctx the parse tree
   */
  void enterConstructor_dec(Smtlibv2Parser.Constructor_decContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#constructor_dec}.
   *
   * @param ctx the parse tree
   */
  void exitConstructor_dec(Smtlibv2Parser.Constructor_decContext ctx);

  /**
   * Enter a parse tree produced by the {@code data_constr} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   */
  void enterData_constr(Smtlibv2Parser.Data_constrContext ctx);

  /**
   * Exit a parse tree produced by the {@code data_constr} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   */
  void exitData_constr(Smtlibv2Parser.Data_constrContext ctx);

  /**
   * Enter a parse tree produced by the {@code data_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   */
  void enterData_multisymb(Smtlibv2Parser.Data_multisymbContext ctx);

  /**
   * Exit a parse tree produced by the {@code data_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   */
  void exitData_multisymb(Smtlibv2Parser.Data_multisymbContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#function_dec}.
   *
   * @param ctx the parse tree
   */
  void enterFunction_dec(Smtlibv2Parser.Function_decContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#function_dec}.
   *
   * @param ctx the parse tree
   */
  void exitFunction_dec(Smtlibv2Parser.Function_decContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#function_def}.
   *
   * @param ctx the parse tree
   */
  void enterFunction_def(Smtlibv2Parser.Function_defContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#function_def}.
   *
   * @param ctx the parse tree
   */
  void exitFunction_def(Smtlibv2Parser.Function_defContext ctx);

  /**
   * Enter a parse tree produced by the {@code prop_symb} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   */
  void enterProp_symb(Smtlibv2Parser.Prop_symbContext ctx);

  /**
   * Exit a parse tree produced by the {@code prop_symb} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   */
  void exitProp_symb(Smtlibv2Parser.Prop_symbContext ctx);

  /**
   * Enter a parse tree produced by the {@code prop_not} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   */
  void enterProp_not(Smtlibv2Parser.Prop_notContext ctx);

  /**
   * Exit a parse tree produced by the {@code prop_not} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   */
  void exitProp_not(Smtlibv2Parser.Prop_notContext ctx);

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
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_assert}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_assert(Smtlibv2Parser.Cmd_assertContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_assert}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_assert(Smtlibv2Parser.Cmd_assertContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_checkSat}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_checkSat(Smtlibv2Parser.Cmd_checkSatContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_checkSat}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_checkSat(Smtlibv2Parser.Cmd_checkSatContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_checkSatAssuming}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_checkSatAssuming(Smtlibv2Parser.Cmd_checkSatAssumingContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_checkSatAssuming}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_checkSatAssuming(Smtlibv2Parser.Cmd_checkSatAssumingContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_declareConst}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_declareConst(Smtlibv2Parser.Cmd_declareConstContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_declareConst}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_declareConst(Smtlibv2Parser.Cmd_declareConstContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatype}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_declareDatatype(Smtlibv2Parser.Cmd_declareDatatypeContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatype}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_declareDatatype(Smtlibv2Parser.Cmd_declareDatatypeContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatypes}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_declareDatatypes(Smtlibv2Parser.Cmd_declareDatatypesContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatypes}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_declareDatatypes(Smtlibv2Parser.Cmd_declareDatatypesContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_declareFun}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_declareFun(Smtlibv2Parser.Cmd_declareFunContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_declareFun}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_declareFun(Smtlibv2Parser.Cmd_declareFunContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_declareSort}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_declareSort(Smtlibv2Parser.Cmd_declareSortContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_declareSort}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_declareSort(Smtlibv2Parser.Cmd_declareSortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_defineFun}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_defineFun(Smtlibv2Parser.Cmd_defineFunContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFun}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_defineFun(Smtlibv2Parser.Cmd_defineFunContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunRec}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_defineFunRec(Smtlibv2Parser.Cmd_defineFunRecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunRec}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_defineFunRec(Smtlibv2Parser.Cmd_defineFunRecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunsRec}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_defineFunsRec(Smtlibv2Parser.Cmd_defineFunsRecContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunsRec}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_defineFunsRec(Smtlibv2Parser.Cmd_defineFunsRecContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_defineSort}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_defineSort(Smtlibv2Parser.Cmd_defineSortContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_defineSort}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_defineSort(Smtlibv2Parser.Cmd_defineSortContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_echo}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_echo(Smtlibv2Parser.Cmd_echoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_echo}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_echo(Smtlibv2Parser.Cmd_echoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_exit}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_exit(Smtlibv2Parser.Cmd_exitContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_exit}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_exit(Smtlibv2Parser.Cmd_exitContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getAssertions}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getAssertions(Smtlibv2Parser.Cmd_getAssertionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getAssertions}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getAssertions(Smtlibv2Parser.Cmd_getAssertionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getAssignment}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getAssignment(Smtlibv2Parser.Cmd_getAssignmentContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getAssignment}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getAssignment(Smtlibv2Parser.Cmd_getAssignmentContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getInfo}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getInfo(Smtlibv2Parser.Cmd_getInfoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getInfo}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getInfo(Smtlibv2Parser.Cmd_getInfoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getModel}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getModel(Smtlibv2Parser.Cmd_getModelContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getModel}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getModel(Smtlibv2Parser.Cmd_getModelContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getOption}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getOption(Smtlibv2Parser.Cmd_getOptionContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getOption}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getOption(Smtlibv2Parser.Cmd_getOptionContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getProof}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getProof(Smtlibv2Parser.Cmd_getProofContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getProof}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getProof(Smtlibv2Parser.Cmd_getProofContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatAssumptions}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getUnsatAssumptions(Smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatAssumptions}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getUnsatAssumptions(Smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatCore}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getUnsatCore(Smtlibv2Parser.Cmd_getUnsatCoreContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatCore}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getUnsatCore(Smtlibv2Parser.Cmd_getUnsatCoreContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_getValue}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_getValue(Smtlibv2Parser.Cmd_getValueContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_getValue}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_getValue(Smtlibv2Parser.Cmd_getValueContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_pop}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_pop(Smtlibv2Parser.Cmd_popContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_pop}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_pop(Smtlibv2Parser.Cmd_popContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_push}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_push(Smtlibv2Parser.Cmd_pushContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_push}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_push(Smtlibv2Parser.Cmd_pushContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_reset}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_reset(Smtlibv2Parser.Cmd_resetContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_reset}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_reset(Smtlibv2Parser.Cmd_resetContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_resetAssertions}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_resetAssertions(Smtlibv2Parser.Cmd_resetAssertionsContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_resetAssertions}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_resetAssertions(Smtlibv2Parser.Cmd_resetAssertionsContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_setInfo}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_setInfo(Smtlibv2Parser.Cmd_setInfoContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_setInfo}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_setInfo(Smtlibv2Parser.Cmd_setInfoContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_setLogic}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_setLogic(Smtlibv2Parser.Cmd_setLogicContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_setLogic}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_setLogic(Smtlibv2Parser.Cmd_setLogicContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#cmd_setOption}.
   *
   * @param ctx the parse tree
   */
  void enterCmd_setOption(Smtlibv2Parser.Cmd_setOptionContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#cmd_setOption}.
   *
   * @param ctx the parse tree
   */
  void exitCmd_setOption(Smtlibv2Parser.Cmd_setOptionContext ctx);

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
   * Enter a parse tree produced by the {@code check_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterCheck_assume(Smtlibv2Parser.Check_assumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code check_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitCheck_assume(Smtlibv2Parser.Check_assumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code decl_const} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecl_const(Smtlibv2Parser.Decl_constContext ctx);

  /**
   * Exit a parse tree produced by the {@code decl_const} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecl_const(Smtlibv2Parser.Decl_constContext ctx);

  /**
   * Enter a parse tree produced by the {@code decl_data} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecl_data(Smtlibv2Parser.Decl_dataContext ctx);

  /**
   * Exit a parse tree produced by the {@code decl_data} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecl_data(Smtlibv2Parser.Decl_dataContext ctx);

  /**
   * Enter a parse tree produced by the {@code decl_datas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecl_datas(Smtlibv2Parser.Decl_datasContext ctx);

  /**
   * Exit a parse tree produced by the {@code decl_datas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecl_datas(Smtlibv2Parser.Decl_datasContext ctx);

  /**
   * Enter a parse tree produced by the {@code decl_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecl_fun(Smtlibv2Parser.Decl_funContext ctx);

  /**
   * Exit a parse tree produced by the {@code decl_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecl_fun(Smtlibv2Parser.Decl_funContext ctx);

  /**
   * Enter a parse tree produced by the {@code decl_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDecl_sort(Smtlibv2Parser.Decl_sortContext ctx);

  /**
   * Exit a parse tree produced by the {@code decl_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDecl_sort(Smtlibv2Parser.Decl_sortContext ctx);

  /**
   * Enter a parse tree produced by the {@code def_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDef_fun(Smtlibv2Parser.Def_funContext ctx);

  /**
   * Exit a parse tree produced by the {@code def_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDef_fun(Smtlibv2Parser.Def_funContext ctx);

  /**
   * Enter a parse tree produced by the {@code def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDef_fun_rec(Smtlibv2Parser.Def_fun_recContext ctx);

  /**
   * Exit a parse tree produced by the {@code def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDef_fun_rec(Smtlibv2Parser.Def_fun_recContext ctx);

  /**
   * Enter a parse tree produced by the {@code def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDef_funs_rec(Smtlibv2Parser.Def_funs_recContext ctx);

  /**
   * Exit a parse tree produced by the {@code def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDef_funs_rec(Smtlibv2Parser.Def_funs_recContext ctx);

  /**
   * Enter a parse tree produced by the {@code def_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterDef_sort(Smtlibv2Parser.Def_sortContext ctx);

  /**
   * Exit a parse tree produced by the {@code def_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitDef_sort(Smtlibv2Parser.Def_sortContext ctx);

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
   * Enter a parse tree produced by the {@code get_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_assert(Smtlibv2Parser.Get_assertContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_assert(Smtlibv2Parser.Get_assertContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_assign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_assign(Smtlibv2Parser.Get_assignContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_assign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_assign(Smtlibv2Parser.Get_assignContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_info} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_info(Smtlibv2Parser.Get_infoContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_info} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_info(Smtlibv2Parser.Get_infoContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_model} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_model(Smtlibv2Parser.Get_modelContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_model} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_model(Smtlibv2Parser.Get_modelContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_option(Smtlibv2Parser.Get_optionContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_option(Smtlibv2Parser.Get_optionContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_proof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_proof(Smtlibv2Parser.Get_proofContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_proof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_proof(Smtlibv2Parser.Get_proofContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_unsat_assume(Smtlibv2Parser.Get_unsat_assumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_unsat_assume(Smtlibv2Parser.Get_unsat_assumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_unsat_core(Smtlibv2Parser.Get_unsat_coreContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_unsat_core(Smtlibv2Parser.Get_unsat_coreContext ctx);

  /**
   * Enter a parse tree produced by the {@code get_val} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterGet_val(Smtlibv2Parser.Get_valContext ctx);

  /**
   * Exit a parse tree produced by the {@code get_val} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitGet_val(Smtlibv2Parser.Get_valContext ctx);

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
   * Enter a parse tree produced by the {@code reset_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterReset_assert(Smtlibv2Parser.Reset_assertContext ctx);

  /**
   * Exit a parse tree produced by the {@code reset_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitReset_assert(Smtlibv2Parser.Reset_assertContext ctx);

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
   * Enter a parse tree produced by the {@code set_logic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterSet_logic(Smtlibv2Parser.Set_logicContext ctx);

  /**
   * Exit a parse tree produced by the {@code set_logic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitSet_logic(Smtlibv2Parser.Set_logicContext ctx);

  /**
   * Enter a parse tree produced by the {@code set_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void enterSet_option(Smtlibv2Parser.Set_optionContext ctx);

  /**
   * Exit a parse tree produced by the {@code set_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   */
  void exitSet_option(Smtlibv2Parser.Set_optionContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#b_value}.
   *
   * @param ctx the parse tree
   */
  void enterB_value(Smtlibv2Parser.B_valueContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#b_value}.
   *
   * @param ctx the parse tree
   */
  void exitB_value(Smtlibv2Parser.B_valueContext ctx);

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
   * Enter a parse tree produced by the {@code print_succ} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterPrint_succ(Smtlibv2Parser.Print_succContext ctx);

  /**
   * Exit a parse tree produced by the {@code print_succ} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitPrint_succ(Smtlibv2Parser.Print_succContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_assert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_assert(Smtlibv2Parser.Prod_assertContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_assert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_assert(Smtlibv2Parser.Prod_assertContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_assign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_assign(Smtlibv2Parser.Prod_assignContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_assign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_assign(Smtlibv2Parser.Prod_assignContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_mod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_mod(Smtlibv2Parser.Prod_modContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_mod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_mod(Smtlibv2Parser.Prod_modContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_proofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_proofs(Smtlibv2Parser.Prod_proofsContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_proofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_proofs(Smtlibv2Parser.Prod_proofsContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_unsat_assume(Smtlibv2Parser.Prod_unsat_assumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_unsat_assume(Smtlibv2Parser.Prod_unsat_assumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code prod_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterProd_unsat_core(Smtlibv2Parser.Prod_unsat_coreContext ctx);

  /**
   * Exit a parse tree produced by the {@code prod_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitProd_unsat_core(Smtlibv2Parser.Prod_unsat_coreContext ctx);

  /**
   * Enter a parse tree produced by the {@code rand_seed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterRand_seed(Smtlibv2Parser.Rand_seedContext ctx);

  /**
   * Exit a parse tree produced by the {@code rand_seed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitRand_seed(Smtlibv2Parser.Rand_seedContext ctx);

  /**
   * Enter a parse tree produced by the {@code reg_out} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterReg_out(Smtlibv2Parser.Reg_outContext ctx);

  /**
   * Exit a parse tree produced by the {@code reg_out} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitReg_out(Smtlibv2Parser.Reg_outContext ctx);

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
   * Enter a parse tree produced by the {@code opt_attr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void enterOpt_attr(Smtlibv2Parser.Opt_attrContext ctx);

  /**
   * Exit a parse tree produced by the {@code opt_attr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   */
  void exitOpt_attr(Smtlibv2Parser.Opt_attrContext ctx);

  /**
   * Enter a parse tree produced by the {@code all_stat} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterAll_stat(Smtlibv2Parser.All_statContext ctx);

  /**
   * Exit a parse tree produced by the {@code all_stat} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitAll_stat(Smtlibv2Parser.All_statContext ctx);

  /**
   * Enter a parse tree produced by the {@code assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterAssert_stack(Smtlibv2Parser.Assert_stackContext ctx);

  /**
   * Exit a parse tree produced by the {@code assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitAssert_stack(Smtlibv2Parser.Assert_stackContext ctx);

  /**
   * Enter a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Exit a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Enter a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Exit a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Enter a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterName(Smtlibv2Parser.NameContext ctx);

  /**
   * Exit a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitName(Smtlibv2Parser.NameContext ctx);

  /**
   * Enter a parse tree produced by the {@code r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterR_unknown(Smtlibv2Parser.R_unknownContext ctx);

  /**
   * Exit a parse tree produced by the {@code r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitR_unknown(Smtlibv2Parser.R_unknownContext ctx);

  /**
   * Enter a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Exit a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_key} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_key(Smtlibv2Parser.Info_keyContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_key} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_key(Smtlibv2Parser.Info_keyContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#error_behaviour}.
   *
   * @param ctx the parse tree
   */
  void enterError_behaviour(Smtlibv2Parser.Error_behaviourContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#error_behaviour}.
   *
   * @param ctx the parse tree
   */
  void exitError_behaviour(Smtlibv2Parser.Error_behaviourContext ctx);

  /**
   * Enter a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void enterMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Exit a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void exitMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Enter a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void enterIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Exit a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void exitIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Enter a parse tree produced by the {@code r_unnown_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void enterR_unnown_s_expr(Smtlibv2Parser.R_unnown_s_exprContext ctx);

  /**
   * Exit a parse tree produced by the {@code r_unnown_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   */
  void exitR_unnown_s_expr(Smtlibv2Parser.R_unnown_s_exprContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_def_fun} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_def_fun(Smtlibv2Parser.Resp_def_funContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_def_fun} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_def_fun(Smtlibv2Parser.Resp_def_funContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_def_fun_rec(Smtlibv2Parser.Resp_def_fun_recContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_def_fun_rec(Smtlibv2Parser.Resp_def_fun_recContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_def_funs_rec(Smtlibv2Parser.Resp_def_funs_recContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_def_funs_rec(Smtlibv2Parser.Resp_def_funs_recContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_assert_stack(Smtlibv2Parser.Info_assert_stackContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_assert_stack(Smtlibv2Parser.Info_assert_stackContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_authors} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_authors(Smtlibv2Parser.Info_authorsContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_authors} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_authors(Smtlibv2Parser.Info_authorsContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_error} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_error(Smtlibv2Parser.Info_errorContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_error} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_error(Smtlibv2Parser.Info_errorContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_name} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_name(Smtlibv2Parser.Info_nameContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_name} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_name(Smtlibv2Parser.Info_nameContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_r_unknown(Smtlibv2Parser.Info_r_unknownContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_r_unknown(Smtlibv2Parser.Info_r_unknownContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_version} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_version(Smtlibv2Parser.Info_versionContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_version} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_version(Smtlibv2Parser.Info_versionContext ctx);

  /**
   * Enter a parse tree produced by the {@code info_attr} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void enterInfo_attr(Smtlibv2Parser.Info_attrContext ctx);

  /**
   * Exit a parse tree produced by the {@code info_attr} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   */
  void exitInfo_attr(Smtlibv2Parser.Info_attrContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#valuation_pair}.
   *
   * @param ctx the parse tree
   */
  void enterValuation_pair(Smtlibv2Parser.Valuation_pairContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#valuation_pair}.
   *
   * @param ctx the parse tree
   */
  void exitValuation_pair(Smtlibv2Parser.Valuation_pairContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#t_valuation_pair}.
   *
   * @param ctx the parse tree
   */
  void enterT_valuation_pair(Smtlibv2Parser.T_valuation_pairContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#t_valuation_pair}.
   *
   * @param ctx the parse tree
   */
  void exitT_valuation_pair(Smtlibv2Parser.T_valuation_pairContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#check_sat_response}.
   *
   * @param ctx the parse tree
   */
  void enterCheck_sat_response(Smtlibv2Parser.Check_sat_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#check_sat_response}.
   *
   * @param ctx the parse tree
   */
  void exitCheck_sat_response(Smtlibv2Parser.Check_sat_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#echo_response}.
   *
   * @param ctx the parse tree
   */
  void enterEcho_response(Smtlibv2Parser.Echo_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#echo_response}.
   *
   * @param ctx the parse tree
   */
  void exitEcho_response(Smtlibv2Parser.Echo_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_assertions_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_assertions_response(Smtlibv2Parser.Get_assertions_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_assertions_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_assertions_response(Smtlibv2Parser.Get_assertions_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_assignment_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_assignment_response(Smtlibv2Parser.Get_assignment_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_assignment_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_assignment_response(Smtlibv2Parser.Get_assignment_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_info_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_info_response(Smtlibv2Parser.Get_info_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_info_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_info_response(Smtlibv2Parser.Get_info_responseContext ctx);

  /**
   * Enter a parse tree produced by the {@code rs_model} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   */
  void enterRs_model(Smtlibv2Parser.Rs_modelContext ctx);

  /**
   * Exit a parse tree produced by the {@code rs_model} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   */
  void exitRs_model(Smtlibv2Parser.Rs_modelContext ctx);

  /**
   * Enter a parse tree produced by the {@code model_resp} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   */
  void enterModel_resp(Smtlibv2Parser.Model_respContext ctx);

  /**
   * Exit a parse tree produced by the {@code model_resp} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   */
  void exitModel_resp(Smtlibv2Parser.Model_respContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_option_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_option_response(Smtlibv2Parser.Get_option_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_option_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_option_response(Smtlibv2Parser.Get_option_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_proof_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_proof_response(Smtlibv2Parser.Get_proof_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_proof_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_proof_response(Smtlibv2Parser.Get_proof_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_unsat_assump_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_unsat_assump_response(Smtlibv2Parser.Get_unsat_assump_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_unsat_assump_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_unsat_assump_response(Smtlibv2Parser.Get_unsat_assump_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_unsat_core_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_unsat_core_response(Smtlibv2Parser.Get_unsat_core_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_unsat_core_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_unsat_core_response(Smtlibv2Parser.Get_unsat_core_responseContext ctx);

  /**
   * Enter a parse tree produced by {@link Smtlibv2Parser#get_value_response}.
   *
   * @param ctx the parse tree
   */
  void enterGet_value_response(Smtlibv2Parser.Get_value_responseContext ctx);

  /**
   * Exit a parse tree produced by {@link Smtlibv2Parser#get_value_response}.
   *
   * @param ctx the parse tree
   */
  void exitGet_value_response(Smtlibv2Parser.Get_value_responseContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_check_sat} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_check_sat(Smtlibv2Parser.Resp_check_satContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_check_sat} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_check_sat(Smtlibv2Parser.Resp_check_satContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_echo} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_echo(Smtlibv2Parser.Resp_echoContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_echo} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_echo(Smtlibv2Parser.Resp_echoContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_get_assert} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_get_assert(Smtlibv2Parser.Resp_get_assertContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_get_assert} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_get_assert(Smtlibv2Parser.Resp_get_assertContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_gett_assign} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_gett_assign(Smtlibv2Parser.Resp_gett_assignContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_gett_assign} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_gett_assign(Smtlibv2Parser.Resp_gett_assignContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_get_info} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_get_info(Smtlibv2Parser.Resp_get_infoContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_get_info} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_get_info(Smtlibv2Parser.Resp_get_infoContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_get_model} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_get_model(Smtlibv2Parser.Resp_get_modelContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_get_model} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_get_model(Smtlibv2Parser.Resp_get_modelContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_option} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_option(Smtlibv2Parser.Resp_optionContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_option} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_option(Smtlibv2Parser.Resp_optionContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_proof} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_proof(Smtlibv2Parser.Resp_proofContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_proof} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_proof(Smtlibv2Parser.Resp_proofContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_unsat_assume(Smtlibv2Parser.Resp_unsat_assumeContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_unsat_assume(Smtlibv2Parser.Resp_unsat_assumeContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_unsat_core(Smtlibv2Parser.Resp_unsat_coreContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_unsat_core(Smtlibv2Parser.Resp_unsat_coreContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_value} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_value(Smtlibv2Parser.Resp_valueContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_value} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_value(Smtlibv2Parser.Resp_valueContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_success} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_success(Smtlibv2Parser.Resp_successContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_success} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_success(Smtlibv2Parser.Resp_successContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_spec_successs} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_spec_successs(Smtlibv2Parser.Resp_spec_successsContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_spec_successs} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_spec_successs(Smtlibv2Parser.Resp_spec_successsContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_unsupported} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_unsupported(Smtlibv2Parser.Resp_unsupportedContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_unsupported} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_unsupported(Smtlibv2Parser.Resp_unsupportedContext ctx);

  /**
   * Enter a parse tree produced by the {@code resp_error} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void enterResp_error(Smtlibv2Parser.Resp_errorContext ctx);

  /**
   * Exit a parse tree produced by the {@code resp_error} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   */
  void exitResp_error(Smtlibv2Parser.Resp_errorContext ctx);
}
