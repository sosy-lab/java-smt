/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

// Generated from
// /home/davidg/IdeaProjects/java-smt/src/org/sosy_lab/
// java_smt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
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
   * Visit a parse tree produced by the {@code start_logic} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStart_logic(Smtlibv2Parser.Start_logicContext ctx);

  /**
   * Visit a parse tree produced by the {@code start_theory} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStart_theory(Smtlibv2Parser.Start_theoryContext ctx);

  /**
   * Visit a parse tree produced by the {@code start_script} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStart_script(Smtlibv2Parser.Start_scriptContext ctx);

  /**
   * Visit a parse tree produced by the {@code start_gen_resp} labeled alternative in {@link
   * Smtlibv2Parser#start}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitStart_gen_resp(Smtlibv2Parser.Start_gen_respContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#generalReservedWord}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGeneralReservedWord(Smtlibv2Parser.GeneralReservedWordContext ctx);

  /**
   * Visit a parse tree produced by the {@code simp_pre_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSimp_pre_symb(Smtlibv2Parser.Simp_pre_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code simp_undef_symb} labeled alternative in {@link
   * Smtlibv2Parser#simpleSymbol}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSimp_undef_symb(Smtlibv2Parser.Simp_undef_symbContext ctx);

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
   * Visit a parse tree produced by the {@code pre_key} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPre_key(Smtlibv2Parser.Pre_keyContext ctx);

  /**
   * Visit a parse tree produced by the {@code key_simsymb} labeled alternative in {@link
   * Smtlibv2Parser#keyword}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitKey_simsymb(Smtlibv2Parser.Key_simsymbContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_num} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_num(Smtlibv2Parser.Spec_constant_numContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_dec} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_dec(Smtlibv2Parser.Spec_constant_decContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_hex} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_hex(Smtlibv2Parser.Spec_constant_hexContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_bin} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_bin(Smtlibv2Parser.Spec_constant_binContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_string} labeled alternative in {@link
   * Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_string(Smtlibv2Parser.Spec_constant_stringContext ctx);

  /**
   * Visit a parse tree produced by the {@code spec_constant_floating_point} labeled alternative in
   * {@link Smtlibv2Parser#spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSpec_constant_floating_point(Smtlibv2Parser.Spec_constant_floating_pointContext ctx);

  /**
   * Visit a parse tree produced by the {@code s_expr_spec} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitS_expr_spec(Smtlibv2Parser.S_expr_specContext ctx);

  /**
   * Visit a parse tree produced by the {@code s_expr_symb} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitS_expr_symb(Smtlibv2Parser.S_expr_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code s_expr_key} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitS_expr_key(Smtlibv2Parser.S_expr_keyContext ctx);

  /**
   * Visit a parse tree produced by the {@code multi_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#s_expr}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMulti_s_expr(Smtlibv2Parser.Multi_s_exprContext ctx);

  /**
   * Visit a parse tree produced by the {@code idx_num} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdx_num(Smtlibv2Parser.Idx_numContext ctx);

  /**
   * Visit a parse tree produced by the {@code idx_symb} labeled alternative in {@link
   * Smtlibv2Parser#index}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIdx_symb(Smtlibv2Parser.Idx_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code id_symb} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitId_symb(Smtlibv2Parser.Id_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code id_symb_idx} labeled alternative in {@link
   * Smtlibv2Parser#identifier}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitId_symb_idx(Smtlibv2Parser.Id_symb_idxContext ctx);

  /**
   * Visit a parse tree produced by the {@code attr_spec} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttr_spec(Smtlibv2Parser.Attr_specContext ctx);

  /**
   * Visit a parse tree produced by the {@code attr_symb} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttr_symb(Smtlibv2Parser.Attr_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code attr_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#attribute_value}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttr_s_expr(Smtlibv2Parser.Attr_s_exprContext ctx);

  /**
   * Visit a parse tree produced by the {@code attr_key} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttr_key(Smtlibv2Parser.Attr_keyContext ctx);

  /**
   * Visit a parse tree produced by the {@code attr_key_attr} labeled alternative in {@link
   * Smtlibv2Parser#attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAttr_key_attr(Smtlibv2Parser.Attr_key_attrContext ctx);

  /**
   * Visit a parse tree produced by the {@code sort_id} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSort_id(Smtlibv2Parser.Sort_idContext ctx);

  /**
   * Visit a parse tree produced by the {@code multisort} labeled alternative in {@link
   * Smtlibv2Parser#sort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMultisort(Smtlibv2Parser.MultisortContext ctx);

  /**
   * Visit a parse tree produced by the {@code qual_id} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQual_id(Smtlibv2Parser.Qual_idContext ctx);

  /**
   * Visit a parse tree produced by the {@code qual_id_sort} labeled alternative in {@link
   * Smtlibv2Parser#qual_identifer}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitQual_id_sort(Smtlibv2Parser.Qual_id_sortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#var_binding}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVar_binding(Smtlibv2Parser.Var_bindingContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sorted_var}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSorted_var(Smtlibv2Parser.Sorted_varContext ctx);

  /**
   * Visit a parse tree produced by the {@code pattern_symb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPattern_symb(Smtlibv2Parser.Pattern_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code pattern_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#pattern}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPattern_multisymb(Smtlibv2Parser.Pattern_multisymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#match_case}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMatch_case(Smtlibv2Parser.Match_caseContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_spec_const} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_spec_const(Smtlibv2Parser.Term_spec_constContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_qual_id} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_qual_id(Smtlibv2Parser.Term_qual_idContext ctx);

  /**
   * Visit a parse tree produced by the {@code multiterm} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMultiterm(Smtlibv2Parser.MultitermContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_let} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_let(Smtlibv2Parser.Term_letContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_forall} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_forall(Smtlibv2Parser.Term_forallContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_exists} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_exists(Smtlibv2Parser.Term_existsContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_match} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_match(Smtlibv2Parser.Term_matchContext ctx);

  /**
   * Visit a parse tree produced by the {@code term_exclam} labeled alternative in {@link
   * Smtlibv2Parser#term}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTerm_exclam(Smtlibv2Parser.Term_exclamContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sort_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSort_symbol_decl(Smtlibv2Parser.Sort_symbol_declContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#meta_spec_constant}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMeta_spec_constant(Smtlibv2Parser.Meta_spec_constantContext ctx);

  /**
   * Visit a parse tree produced by the {@code fun_symb_spec} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFun_symb_spec(Smtlibv2Parser.Fun_symb_specContext ctx);

  /**
   * Visit a parse tree produced by the {@code fun_symb_meta} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFun_symb_meta(Smtlibv2Parser.Fun_symb_metaContext ctx);

  /**
   * Visit a parse tree produced by the {@code fun_symb_id} labeled alternative in {@link
   * Smtlibv2Parser#fun_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFun_symb_id(Smtlibv2Parser.Fun_symb_idContext ctx);

  /**
   * Visit a parse tree produced by the {@code par_fun_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPar_fun_symb(Smtlibv2Parser.Par_fun_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code par_fun_multi_symb} labeled alternative in {@link
   * Smtlibv2Parser#par_fun_symbol_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPar_fun_multi_symb(Smtlibv2Parser.Par_fun_multi_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_sort} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_sort(Smtlibv2Parser.Theory_sortContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_fun} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_fun(Smtlibv2Parser.Theory_funContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_sort_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_sort_descr(Smtlibv2Parser.Theory_sort_descrContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_fun_descr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_fun_descr(Smtlibv2Parser.Theory_fun_descrContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_def} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_def(Smtlibv2Parser.Theory_defContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_val} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_val(Smtlibv2Parser.Theory_valContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_notes} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_notes(Smtlibv2Parser.Theory_notesContext ctx);

  /**
   * Visit a parse tree produced by the {@code theory_attr} labeled alternative in {@link
   * Smtlibv2Parser#theory_attribute}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_attr(Smtlibv2Parser.Theory_attrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#theory_decl}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitTheory_decl(Smtlibv2Parser.Theory_declContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_theory} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_theory(Smtlibv2Parser.Logic_theoryContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_language} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_language(Smtlibv2Parser.Logic_languageContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_ext} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_ext(Smtlibv2Parser.Logic_extContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_val} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_val(Smtlibv2Parser.Logic_valContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_notes} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_notes(Smtlibv2Parser.Logic_notesContext ctx);

  /**
   * Visit a parse tree produced by the {@code logic_attr} labeled alternative in {@link
   * Smtlibv2Parser#logic_attribue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic_attr(Smtlibv2Parser.Logic_attrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#logic}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitLogic(Smtlibv2Parser.LogicContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#sort_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSort_dec(Smtlibv2Parser.Sort_decContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#selector_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSelector_dec(Smtlibv2Parser.Selector_decContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#constructor_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitConstructor_dec(Smtlibv2Parser.Constructor_decContext ctx);

  /**
   * Visit a parse tree produced by the {@code data_constr} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitData_constr(Smtlibv2Parser.Data_constrContext ctx);

  /**
   * Visit a parse tree produced by the {@code data_multisymb} labeled alternative in {@link
   * Smtlibv2Parser#datatype_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitData_multisymb(Smtlibv2Parser.Data_multisymbContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#function_dec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunction_dec(Smtlibv2Parser.Function_decContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#function_def}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitFunction_def(Smtlibv2Parser.Function_defContext ctx);

  /**
   * Visit a parse tree produced by the {@code prop_symb} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProp_symb(Smtlibv2Parser.Prop_symbContext ctx);

  /**
   * Visit a parse tree produced by the {@code prop_not} labeled alternative in {@link
   * Smtlibv2Parser#prop_literal}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProp_not(Smtlibv2Parser.Prop_notContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#script}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitScript(Smtlibv2Parser.ScriptContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_assert}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_assert(Smtlibv2Parser.Cmd_assertContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_checkSat}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_checkSat(Smtlibv2Parser.Cmd_checkSatContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_checkSatAssuming}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_checkSatAssuming(Smtlibv2Parser.Cmd_checkSatAssumingContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_declareConst}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_declareConst(Smtlibv2Parser.Cmd_declareConstContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatype}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_declareDatatype(Smtlibv2Parser.Cmd_declareDatatypeContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_declareDatatypes}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_declareDatatypes(Smtlibv2Parser.Cmd_declareDatatypesContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_declareFun}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_declareFun(Smtlibv2Parser.Cmd_declareFunContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_declareSort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_declareSort(Smtlibv2Parser.Cmd_declareSortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFun}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_defineFun(Smtlibv2Parser.Cmd_defineFunContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunRec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_defineFunRec(Smtlibv2Parser.Cmd_defineFunRecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_defineFunsRec}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_defineFunsRec(Smtlibv2Parser.Cmd_defineFunsRecContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_defineSort}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_defineSort(Smtlibv2Parser.Cmd_defineSortContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_echo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_echo(Smtlibv2Parser.Cmd_echoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_exit}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_exit(Smtlibv2Parser.Cmd_exitContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getAssertions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getAssertions(Smtlibv2Parser.Cmd_getAssertionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getAssignment}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getAssignment(Smtlibv2Parser.Cmd_getAssignmentContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getInfo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getInfo(Smtlibv2Parser.Cmd_getInfoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getModel}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getModel(Smtlibv2Parser.Cmd_getModelContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getOption}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getOption(Smtlibv2Parser.Cmd_getOptionContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getProof}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getProof(Smtlibv2Parser.Cmd_getProofContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatAssumptions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getUnsatAssumptions(Smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getUnsatCore}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getUnsatCore(Smtlibv2Parser.Cmd_getUnsatCoreContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_getValue}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_getValue(Smtlibv2Parser.Cmd_getValueContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_pop}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_pop(Smtlibv2Parser.Cmd_popContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_push}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_push(Smtlibv2Parser.Cmd_pushContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_reset}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_reset(Smtlibv2Parser.Cmd_resetContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_resetAssertions}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_resetAssertions(Smtlibv2Parser.Cmd_resetAssertionsContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_setInfo}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_setInfo(Smtlibv2Parser.Cmd_setInfoContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_setLogic}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_setLogic(Smtlibv2Parser.Cmd_setLogicContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#cmd_setOption}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCmd_setOption(Smtlibv2Parser.Cmd_setOptionContext ctx);

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
   * Visit a parse tree produced by the {@code check_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCheck_assume(Smtlibv2Parser.Check_assumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code decl_const} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecl_const(Smtlibv2Parser.Decl_constContext ctx);

  /**
   * Visit a parse tree produced by the {@code decl_data} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecl_data(Smtlibv2Parser.Decl_dataContext ctx);

  /**
   * Visit a parse tree produced by the {@code decl_datas} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecl_datas(Smtlibv2Parser.Decl_datasContext ctx);

  /**
   * Visit a parse tree produced by the {@code decl_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecl_fun(Smtlibv2Parser.Decl_funContext ctx);

  /**
   * Visit a parse tree produced by the {@code decl_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDecl_sort(Smtlibv2Parser.Decl_sortContext ctx);

  /**
   * Visit a parse tree produced by the {@code def_fun} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDef_fun(Smtlibv2Parser.Def_funContext ctx);

  /**
   * Visit a parse tree produced by the {@code def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDef_fun_rec(Smtlibv2Parser.Def_fun_recContext ctx);

  /**
   * Visit a parse tree produced by the {@code def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDef_funs_rec(Smtlibv2Parser.Def_funs_recContext ctx);

  /**
   * Visit a parse tree produced by the {@code def_sort} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitDef_sort(Smtlibv2Parser.Def_sortContext ctx);

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
   * Visit a parse tree produced by the {@code get_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_assert(Smtlibv2Parser.Get_assertContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_assign} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_assign(Smtlibv2Parser.Get_assignContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_info} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_info(Smtlibv2Parser.Get_infoContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_model} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_model(Smtlibv2Parser.Get_modelContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_option(Smtlibv2Parser.Get_optionContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_proof} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_proof(Smtlibv2Parser.Get_proofContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_unsat_assume(Smtlibv2Parser.Get_unsat_assumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_unsat_core(Smtlibv2Parser.Get_unsat_coreContext ctx);

  /**
   * Visit a parse tree produced by the {@code get_val} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_val(Smtlibv2Parser.Get_valContext ctx);

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
   * Visit a parse tree produced by the {@code reset_assert} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitReset_assert(Smtlibv2Parser.Reset_assertContext ctx);

  /**
   * Visit a parse tree produced by the {@code setInfo} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSetInfo(Smtlibv2Parser.SetInfoContext ctx);

  /**
   * Visit a parse tree produced by the {@code set_logic} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSet_logic(Smtlibv2Parser.Set_logicContext ctx);

  /**
   * Visit a parse tree produced by the {@code set_option} labeled alternative in {@link
   * Smtlibv2Parser#command}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitSet_option(Smtlibv2Parser.Set_optionContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#b_value}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitB_value(Smtlibv2Parser.B_valueContext ctx);

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
   * Visit a parse tree produced by the {@code print_succ} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitPrint_succ(Smtlibv2Parser.Print_succContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_assert} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_assert(Smtlibv2Parser.Prod_assertContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_assign} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_assign(Smtlibv2Parser.Prod_assignContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_mod} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_mod(Smtlibv2Parser.Prod_modContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_proofs} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_proofs(Smtlibv2Parser.Prod_proofsContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_unsat_assume(Smtlibv2Parser.Prod_unsat_assumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code prod_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitProd_unsat_core(Smtlibv2Parser.Prod_unsat_coreContext ctx);

  /**
   * Visit a parse tree produced by the {@code rand_seed} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRand_seed(Smtlibv2Parser.Rand_seedContext ctx);

  /**
   * Visit a parse tree produced by the {@code reg_out} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitReg_out(Smtlibv2Parser.Reg_outContext ctx);

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
   * Visit a parse tree produced by the {@code opt_attr} labeled alternative in {@link
   * Smtlibv2Parser#option}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitOpt_attr(Smtlibv2Parser.Opt_attrContext ctx);

  /**
   * Visit a parse tree produced by the {@code all_stat} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAll_stat(Smtlibv2Parser.All_statContext ctx);

  /**
   * Visit a parse tree produced by the {@code assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAssert_stack(Smtlibv2Parser.Assert_stackContext ctx);

  /**
   * Visit a parse tree produced by the {@code authors} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitAuthors(Smtlibv2Parser.AuthorsContext ctx);

  /**
   * Visit a parse tree produced by the {@code error} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitError(Smtlibv2Parser.ErrorContext ctx);

  /**
   * Visit a parse tree produced by the {@code name} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitName(Smtlibv2Parser.NameContext ctx);

  /**
   * Visit a parse tree produced by the {@code r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitR_unknown(Smtlibv2Parser.R_unknownContext ctx);

  /**
   * Visit a parse tree produced by the {@code version} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitVersion(Smtlibv2Parser.VersionContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_key} labeled alternative in {@link
   * Smtlibv2Parser#info_flag}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_key(Smtlibv2Parser.Info_keyContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#error_behaviour}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitError_behaviour(Smtlibv2Parser.Error_behaviourContext ctx);

  /**
   * Visit a parse tree produced by the {@code memout} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitMemout(Smtlibv2Parser.MemoutContext ctx);

  /**
   * Visit a parse tree produced by the {@code incomp} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitIncomp(Smtlibv2Parser.IncompContext ctx);

  /**
   * Visit a parse tree produced by the {@code r_unnown_s_expr} labeled alternative in {@link
   * Smtlibv2Parser#reason_unknown}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitR_unnown_s_expr(Smtlibv2Parser.R_unnown_s_exprContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_def_fun} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_def_fun(Smtlibv2Parser.Resp_def_funContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_def_fun_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_def_fun_rec(Smtlibv2Parser.Resp_def_fun_recContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_def_funs_rec} labeled alternative in {@link
   * Smtlibv2Parser#model_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_def_funs_rec(Smtlibv2Parser.Resp_def_funs_recContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_assert_stack} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_assert_stack(Smtlibv2Parser.Info_assert_stackContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_authors} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_authors(Smtlibv2Parser.Info_authorsContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_error} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_error(Smtlibv2Parser.Info_errorContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_name} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_name(Smtlibv2Parser.Info_nameContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_r_unknown} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_r_unknown(Smtlibv2Parser.Info_r_unknownContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_version} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_version(Smtlibv2Parser.Info_versionContext ctx);

  /**
   * Visit a parse tree produced by the {@code info_attr} labeled alternative in {@link
   * Smtlibv2Parser#info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitInfo_attr(Smtlibv2Parser.Info_attrContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#valuation_pair}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitValuation_pair(Smtlibv2Parser.Valuation_pairContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#t_valuation_pair}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitT_valuation_pair(Smtlibv2Parser.T_valuation_pairContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#check_sat_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitCheck_sat_response(Smtlibv2Parser.Check_sat_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#echo_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitEcho_response(Smtlibv2Parser.Echo_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_assertions_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_assertions_response(Smtlibv2Parser.Get_assertions_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_assignment_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_assignment_response(Smtlibv2Parser.Get_assignment_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_info_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_info_response(Smtlibv2Parser.Get_info_responseContext ctx);

  /**
   * Visit a parse tree produced by the {@code rs_model} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitRs_model(Smtlibv2Parser.Rs_modelContext ctx);

  /**
   * Visit a parse tree produced by the {@code model_resp} labeled alternative in {@link
   * Smtlibv2Parser#get_model_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitModel_resp(Smtlibv2Parser.Model_respContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_option_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_option_response(Smtlibv2Parser.Get_option_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_proof_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_proof_response(Smtlibv2Parser.Get_proof_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_unsat_assump_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_unsat_assump_response(Smtlibv2Parser.Get_unsat_assump_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_unsat_core_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_unsat_core_response(Smtlibv2Parser.Get_unsat_core_responseContext ctx);

  /**
   * Visit a parse tree produced by {@link Smtlibv2Parser#get_value_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitGet_value_response(Smtlibv2Parser.Get_value_responseContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_check_sat} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_check_sat(Smtlibv2Parser.Resp_check_satContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_echo} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_echo(Smtlibv2Parser.Resp_echoContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_get_assert} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_get_assert(Smtlibv2Parser.Resp_get_assertContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_gett_assign} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_gett_assign(Smtlibv2Parser.Resp_gett_assignContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_get_info} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_get_info(Smtlibv2Parser.Resp_get_infoContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_get_model} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_get_model(Smtlibv2Parser.Resp_get_modelContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_option} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_option(Smtlibv2Parser.Resp_optionContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_proof} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_proof(Smtlibv2Parser.Resp_proofContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_unsat_assume} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_unsat_assume(Smtlibv2Parser.Resp_unsat_assumeContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_unsat_core} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_unsat_core(Smtlibv2Parser.Resp_unsat_coreContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_value} labeled alternative in {@link
   * Smtlibv2Parser#specific_success_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_value(Smtlibv2Parser.Resp_valueContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_success} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_success(Smtlibv2Parser.Resp_successContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_spec_successs} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_spec_successs(Smtlibv2Parser.Resp_spec_successsContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_unsupported} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_unsupported(Smtlibv2Parser.Resp_unsupportedContext ctx);

  /**
   * Visit a parse tree produced by the {@code resp_error} labeled alternative in {@link
   * Smtlibv2Parser#general_response}.
   *
   * @param ctx the parse tree
   * @return the visitor result
   */
  T visitResp_error(Smtlibv2Parser.Resp_errorContext ctx);
}
