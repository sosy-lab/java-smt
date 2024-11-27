// Generated from /home/dalux/Dokumente/IdeaProjects/java-smt/src/org/sosy_lab/java_smt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parserInterpreter;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link smtlibv2Parser}.
 */
public interface smtlibv2Listener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by the {@code start_logic}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart_logic(smtlibv2Parser.Start_logicContext ctx);
	/**
	 * Exit a parse tree produced by the {@code start_logic}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart_logic(smtlibv2Parser.Start_logicContext ctx);
	/**
	 * Enter a parse tree produced by the {@code start_theory}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart_theory(smtlibv2Parser.Start_theoryContext ctx);
	/**
	 * Exit a parse tree produced by the {@code start_theory}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart_theory(smtlibv2Parser.Start_theoryContext ctx);
	/**
	 * Enter a parse tree produced by the {@code start_script}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart_script(smtlibv2Parser.Start_scriptContext ctx);
	/**
	 * Exit a parse tree produced by the {@code start_script}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart_script(smtlibv2Parser.Start_scriptContext ctx);
	/**
	 * Enter a parse tree produced by the {@code start_gen_resp}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart_gen_resp(smtlibv2Parser.Start_gen_respContext ctx);
	/**
	 * Exit a parse tree produced by the {@code start_gen_resp}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart_gen_resp(smtlibv2Parser.Start_gen_respContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 */
	void enterGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 */
	void exitGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Enter a parse tree produced by the {@code simp_pre_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void enterSimp_pre_symb(smtlibv2Parser.Simp_pre_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code simp_pre_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void exitSimp_pre_symb(smtlibv2Parser.Simp_pre_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code simp_undef_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void enterSimp_undef_symb(smtlibv2Parser.Simp_undef_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code simp_undef_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void exitSimp_undef_symb(smtlibv2Parser.Simp_undef_symbContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 */
	void enterQuotedSymbol(smtlibv2Parser.QuotedSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 */
	void exitQuotedSymbol(smtlibv2Parser.QuotedSymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 */
	void enterPredefSymbol(smtlibv2Parser.PredefSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 */
	void exitPredefSymbol(smtlibv2Parser.PredefSymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 */
	void enterPredefKeyword(smtlibv2Parser.PredefKeywordContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 */
	void exitPredefKeyword(smtlibv2Parser.PredefKeywordContext ctx);
	/**
	 * Enter a parse tree produced by the {@code simpsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void enterSimpsymb(smtlibv2Parser.SimpsymbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code simpsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void exitSimpsymb(smtlibv2Parser.SimpsymbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code quotsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void enterQuotsymb(smtlibv2Parser.QuotsymbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code quotsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void exitQuotsymb(smtlibv2Parser.QuotsymbContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#numeral}.
	 * @param ctx the parse tree
	 */
	void enterNumeral(smtlibv2Parser.NumeralContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#numeral}.
	 * @param ctx the parse tree
	 */
	void exitNumeral(smtlibv2Parser.NumeralContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#decimal}.
	 * @param ctx the parse tree
	 */
	void enterDecimal(smtlibv2Parser.DecimalContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#decimal}.
	 * @param ctx the parse tree
	 */
	void exitDecimal(smtlibv2Parser.DecimalContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 */
	void enterHexadecimal(smtlibv2Parser.HexadecimalContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 */
	void exitHexadecimal(smtlibv2Parser.HexadecimalContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#binary}.
	 * @param ctx the parse tree
	 */
	void enterBinary(smtlibv2Parser.BinaryContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#binary}.
	 * @param ctx the parse tree
	 */
	void exitBinary(smtlibv2Parser.BinaryContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#string}.
	 * @param ctx the parse tree
	 */
	void enterString(smtlibv2Parser.StringContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#string}.
	 * @param ctx the parse tree
	 */
	void exitString(smtlibv2Parser.StringContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#floatingpoint}.
	 * @param ctx the parse tree
	 */
	void enterFloatingpoint(smtlibv2Parser.FloatingpointContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#floatingpoint}.
	 * @param ctx the parse tree
	 */
	void exitFloatingpoint(smtlibv2Parser.FloatingpointContext ctx);
	/**
	 * Enter a parse tree produced by the {@code pre_key}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void enterPre_key(smtlibv2Parser.Pre_keyContext ctx);
	/**
	 * Exit a parse tree produced by the {@code pre_key}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void exitPre_key(smtlibv2Parser.Pre_keyContext ctx);
	/**
	 * Enter a parse tree produced by the {@code key_simsymb}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void enterKey_simsymb(smtlibv2Parser.Key_simsymbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code key_simsymb}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void exitKey_simsymb(smtlibv2Parser.Key_simsymbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_num}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_num(smtlibv2Parser.Spec_constant_numContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_num}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_num(smtlibv2Parser.Spec_constant_numContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_dec}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_dec(smtlibv2Parser.Spec_constant_decContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_dec}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_dec(smtlibv2Parser.Spec_constant_decContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_hex}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_hex(smtlibv2Parser.Spec_constant_hexContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_hex}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_hex(smtlibv2Parser.Spec_constant_hexContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_bin}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_bin(smtlibv2Parser.Spec_constant_binContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_bin}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_bin(smtlibv2Parser.Spec_constant_binContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_string}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_string(smtlibv2Parser.Spec_constant_stringContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_string}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_string(smtlibv2Parser.Spec_constant_stringContext ctx);
	/**
	 * Enter a parse tree produced by the {@code spec_constant_floating_point}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant_floating_point(smtlibv2Parser.Spec_constant_floating_pointContext ctx);
	/**
	 * Exit a parse tree produced by the {@code spec_constant_floating_point}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant_floating_point(smtlibv2Parser.Spec_constant_floating_pointContext ctx);
	/**
	 * Enter a parse tree produced by the {@code s_expr_spec}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterS_expr_spec(smtlibv2Parser.S_expr_specContext ctx);
	/**
	 * Exit a parse tree produced by the {@code s_expr_spec}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitS_expr_spec(smtlibv2Parser.S_expr_specContext ctx);
	/**
	 * Enter a parse tree produced by the {@code s_expr_symb}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterS_expr_symb(smtlibv2Parser.S_expr_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code s_expr_symb}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitS_expr_symb(smtlibv2Parser.S_expr_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code s_expr_key}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterS_expr_key(smtlibv2Parser.S_expr_keyContext ctx);
	/**
	 * Exit a parse tree produced by the {@code s_expr_key}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitS_expr_key(smtlibv2Parser.S_expr_keyContext ctx);
	/**
	 * Enter a parse tree produced by the {@code multi_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterMulti_s_expr(smtlibv2Parser.Multi_s_exprContext ctx);
	/**
	 * Exit a parse tree produced by the {@code multi_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitMulti_s_expr(smtlibv2Parser.Multi_s_exprContext ctx);
	/**
	 * Enter a parse tree produced by the {@code idx_num}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void enterIdx_num(smtlibv2Parser.Idx_numContext ctx);
	/**
	 * Exit a parse tree produced by the {@code idx_num}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void exitIdx_num(smtlibv2Parser.Idx_numContext ctx);
	/**
	 * Enter a parse tree produced by the {@code idx_symb}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void enterIdx_symb(smtlibv2Parser.Idx_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code idx_symb}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void exitIdx_symb(smtlibv2Parser.Idx_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code id_symb}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void enterId_symb(smtlibv2Parser.Id_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code id_symb}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void exitId_symb(smtlibv2Parser.Id_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code id_symb_idx}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void enterId_symb_idx(smtlibv2Parser.Id_symb_idxContext ctx);
	/**
	 * Exit a parse tree produced by the {@code id_symb_idx}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void exitId_symb_idx(smtlibv2Parser.Id_symb_idxContext ctx);
	/**
	 * Enter a parse tree produced by the {@code attr_spec}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void enterAttr_spec(smtlibv2Parser.Attr_specContext ctx);
	/**
	 * Exit a parse tree produced by the {@code attr_spec}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void exitAttr_spec(smtlibv2Parser.Attr_specContext ctx);
	/**
	 * Enter a parse tree produced by the {@code attr_symb}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void enterAttr_symb(smtlibv2Parser.Attr_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code attr_symb}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void exitAttr_symb(smtlibv2Parser.Attr_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code attr_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void enterAttr_s_expr(smtlibv2Parser.Attr_s_exprContext ctx);
	/**
	 * Exit a parse tree produced by the {@code attr_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void exitAttr_s_expr(smtlibv2Parser.Attr_s_exprContext ctx);
	/**
	 * Enter a parse tree produced by the {@code attr_key}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void enterAttr_key(smtlibv2Parser.Attr_keyContext ctx);
	/**
	 * Exit a parse tree produced by the {@code attr_key}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void exitAttr_key(smtlibv2Parser.Attr_keyContext ctx);
	/**
	 * Enter a parse tree produced by the {@code attr_key_attr}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void enterAttr_key_attr(smtlibv2Parser.Attr_key_attrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code attr_key_attr}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void exitAttr_key_attr(smtlibv2Parser.Attr_key_attrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code sort_id}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void enterSort_id(smtlibv2Parser.Sort_idContext ctx);
	/**
	 * Exit a parse tree produced by the {@code sort_id}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void exitSort_id(smtlibv2Parser.Sort_idContext ctx);
	/**
	 * Enter a parse tree produced by the {@code multisort}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void enterMultisort(smtlibv2Parser.MultisortContext ctx);
	/**
	 * Exit a parse tree produced by the {@code multisort}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void exitMultisort(smtlibv2Parser.MultisortContext ctx);
	/**
	 * Enter a parse tree produced by the {@code qual_id}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void enterQual_id(smtlibv2Parser.Qual_idContext ctx);
	/**
	 * Exit a parse tree produced by the {@code qual_id}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void exitQual_id(smtlibv2Parser.Qual_idContext ctx);
	/**
	 * Enter a parse tree produced by the {@code qual_id_sort}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void enterQual_id_sort(smtlibv2Parser.Qual_id_sortContext ctx);
	/**
	 * Exit a parse tree produced by the {@code qual_id_sort}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void exitQual_id_sort(smtlibv2Parser.Qual_id_sortContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#var_binding}.
	 * @param ctx the parse tree
	 */
	void enterVar_binding(smtlibv2Parser.Var_bindingContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#var_binding}.
	 * @param ctx the parse tree
	 */
	void exitVar_binding(smtlibv2Parser.Var_bindingContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 */
	void enterSorted_var(smtlibv2Parser.Sorted_varContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 */
	void exitSorted_var(smtlibv2Parser.Sorted_varContext ctx);
	/**
	 * Enter a parse tree produced by the {@code pattern_symb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void enterPattern_symb(smtlibv2Parser.Pattern_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code pattern_symb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void exitPattern_symb(smtlibv2Parser.Pattern_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code pattern_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void enterPattern_multisymb(smtlibv2Parser.Pattern_multisymbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code pattern_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void exitPattern_multisymb(smtlibv2Parser.Pattern_multisymbContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#match_case}.
	 * @param ctx the parse tree
	 */
	void enterMatch_case(smtlibv2Parser.Match_caseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#match_case}.
	 * @param ctx the parse tree
	 */
	void exitMatch_case(smtlibv2Parser.Match_caseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_spec_const}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_spec_const(smtlibv2Parser.Term_spec_constContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_spec_const}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_spec_const(smtlibv2Parser.Term_spec_constContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_qual_id}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_qual_id(smtlibv2Parser.Term_qual_idContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_qual_id}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_qual_id(smtlibv2Parser.Term_qual_idContext ctx);
	/**
	 * Enter a parse tree produced by the {@code multiterm}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterMultiterm(smtlibv2Parser.MultitermContext ctx);
	/**
	 * Exit a parse tree produced by the {@code multiterm}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitMultiterm(smtlibv2Parser.MultitermContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_let}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_let(smtlibv2Parser.Term_letContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_let}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_let(smtlibv2Parser.Term_letContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_forall}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_forall(smtlibv2Parser.Term_forallContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_forall}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_forall(smtlibv2Parser.Term_forallContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_exists}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_exists(smtlibv2Parser.Term_existsContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_exists}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_exists(smtlibv2Parser.Term_existsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_match}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_match(smtlibv2Parser.Term_matchContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_match}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_match(smtlibv2Parser.Term_matchContext ctx);
	/**
	 * Enter a parse tree produced by the {@code term_exclam}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm_exclam(smtlibv2Parser.Term_exclamContext ctx);
	/**
	 * Exit a parse tree produced by the {@code term_exclam}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm_exclam(smtlibv2Parser.Term_exclamContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterSort_symbol_decl(smtlibv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitSort_symbol_decl(smtlibv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterMeta_spec_constant(smtlibv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitMeta_spec_constant(smtlibv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Enter a parse tree produced by the {@code fun_symb_spec}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterFun_symb_spec(smtlibv2Parser.Fun_symb_specContext ctx);
	/**
	 * Exit a parse tree produced by the {@code fun_symb_spec}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitFun_symb_spec(smtlibv2Parser.Fun_symb_specContext ctx);
	/**
	 * Enter a parse tree produced by the {@code fun_symb_meta}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterFun_symb_meta(smtlibv2Parser.Fun_symb_metaContext ctx);
	/**
	 * Exit a parse tree produced by the {@code fun_symb_meta}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitFun_symb_meta(smtlibv2Parser.Fun_symb_metaContext ctx);
	/**
	 * Enter a parse tree produced by the {@code fun_symb_id}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterFun_symb_id(smtlibv2Parser.Fun_symb_idContext ctx);
	/**
	 * Exit a parse tree produced by the {@code fun_symb_id}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitFun_symb_id(smtlibv2Parser.Fun_symb_idContext ctx);
	/**
	 * Enter a parse tree produced by the {@code par_fun_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterPar_fun_symb(smtlibv2Parser.Par_fun_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code par_fun_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitPar_fun_symb(smtlibv2Parser.Par_fun_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code par_fun_multi_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterPar_fun_multi_symb(smtlibv2Parser.Par_fun_multi_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code par_fun_multi_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitPar_fun_multi_symb(smtlibv2Parser.Par_fun_multi_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_sort}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_sort(smtlibv2Parser.Theory_sortContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_sort}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_sort(smtlibv2Parser.Theory_sortContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_fun}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_fun(smtlibv2Parser.Theory_funContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_fun}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_fun(smtlibv2Parser.Theory_funContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_sort_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_sort_descr(smtlibv2Parser.Theory_sort_descrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_sort_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_sort_descr(smtlibv2Parser.Theory_sort_descrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_fun_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_fun_descr(smtlibv2Parser.Theory_fun_descrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_fun_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_fun_descr(smtlibv2Parser.Theory_fun_descrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_def}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_def(smtlibv2Parser.Theory_defContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_def}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_def(smtlibv2Parser.Theory_defContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_val}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_val(smtlibv2Parser.Theory_valContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_val}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_val(smtlibv2Parser.Theory_valContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_notes}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_notes(smtlibv2Parser.Theory_notesContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_notes}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_notes(smtlibv2Parser.Theory_notesContext ctx);
	/**
	 * Enter a parse tree produced by the {@code theory_attr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_attr(smtlibv2Parser.Theory_attrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code theory_attr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_attr(smtlibv2Parser.Theory_attrContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 */
	void enterTheory_decl(smtlibv2Parser.Theory_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 */
	void exitTheory_decl(smtlibv2Parser.Theory_declContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_theory}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_theory(smtlibv2Parser.Logic_theoryContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_theory}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_theory(smtlibv2Parser.Logic_theoryContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_language}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_language(smtlibv2Parser.Logic_languageContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_language}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_language(smtlibv2Parser.Logic_languageContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_ext}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_ext(smtlibv2Parser.Logic_extContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_ext}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_ext(smtlibv2Parser.Logic_extContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_val}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_val(smtlibv2Parser.Logic_valContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_val}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_val(smtlibv2Parser.Logic_valContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_notes}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_notes(smtlibv2Parser.Logic_notesContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_notes}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_notes(smtlibv2Parser.Logic_notesContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logic_attr}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_attr(smtlibv2Parser.Logic_attrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logic_attr}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_attr(smtlibv2Parser.Logic_attrContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#logic}.
	 * @param ctx the parse tree
	 */
	void enterLogic(smtlibv2Parser.LogicContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#logic}.
	 * @param ctx the parse tree
	 */
	void exitLogic(smtlibv2Parser.LogicContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 */
	void enterSort_dec(smtlibv2Parser.Sort_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 */
	void exitSort_dec(smtlibv2Parser.Sort_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 */
	void enterSelector_dec(smtlibv2Parser.Selector_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 */
	void exitSelector_dec(smtlibv2Parser.Selector_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 */
	void enterConstructor_dec(smtlibv2Parser.Constructor_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 */
	void exitConstructor_dec(smtlibv2Parser.Constructor_decContext ctx);
	/**
	 * Enter a parse tree produced by the {@code data_constr}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void enterData_constr(smtlibv2Parser.Data_constrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code data_constr}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void exitData_constr(smtlibv2Parser.Data_constrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code data_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void enterData_multisymb(smtlibv2Parser.Data_multisymbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code data_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void exitData_multisymb(smtlibv2Parser.Data_multisymbContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#function_dec}.
	 * @param ctx the parse tree
	 */
	void enterFunction_dec(smtlibv2Parser.Function_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#function_dec}.
	 * @param ctx the parse tree
	 */
	void exitFunction_dec(smtlibv2Parser.Function_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#function_def}.
	 * @param ctx the parse tree
	 */
	void enterFunction_def(smtlibv2Parser.Function_defContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#function_def}.
	 * @param ctx the parse tree
	 */
	void exitFunction_def(smtlibv2Parser.Function_defContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prop_symb}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void enterProp_symb(smtlibv2Parser.Prop_symbContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prop_symb}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void exitProp_symb(smtlibv2Parser.Prop_symbContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prop_not}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void enterProp_not(smtlibv2Parser.Prop_notContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prop_not}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void exitProp_not(smtlibv2Parser.Prop_notContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#script}.
	 * @param ctx the parse tree
	 */
	void enterScript(smtlibv2Parser.ScriptContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#script}.
	 * @param ctx the parse tree
	 */
	void exitScript(smtlibv2Parser.ScriptContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 */
	void enterCmd_assert(smtlibv2Parser.Cmd_assertContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 */
	void exitCmd_assert(smtlibv2Parser.Cmd_assertContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 */
	void enterCmd_checkSat(smtlibv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 */
	void exitCmd_checkSat(smtlibv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 */
	void enterCmd_checkSatAssuming(smtlibv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 */
	void exitCmd_checkSatAssuming(smtlibv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareConst(smtlibv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareConst(smtlibv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareDatatype(smtlibv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareDatatype(smtlibv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareDatatypes(smtlibv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareDatatypes(smtlibv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareFun(smtlibv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareFun(smtlibv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareSort(smtlibv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareSort(smtlibv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFun(smtlibv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFun(smtlibv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFunRec(smtlibv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFunRec(smtlibv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFunsRec(smtlibv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFunsRec(smtlibv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineSort(smtlibv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineSort(smtlibv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_echo(smtlibv2Parser.Cmd_echoContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_echo(smtlibv2Parser.Cmd_echoContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 */
	void enterCmd_exit(smtlibv2Parser.Cmd_exitContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 */
	void exitCmd_exit(smtlibv2Parser.Cmd_exitContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getAssertions(smtlibv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getAssertions(smtlibv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getAssignment(smtlibv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getAssignment(smtlibv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getInfo(smtlibv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getInfo(smtlibv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getModel(smtlibv2Parser.Cmd_getModelContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getModel(smtlibv2Parser.Cmd_getModelContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getOption(smtlibv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getOption(smtlibv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getProof(smtlibv2Parser.Cmd_getProofContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getProof(smtlibv2Parser.Cmd_getProofContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getUnsatAssumptions(smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getUnsatAssumptions(smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getUnsatCore(smtlibv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getUnsatCore(smtlibv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getValue(smtlibv2Parser.Cmd_getValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getValue(smtlibv2Parser.Cmd_getValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 */
	void enterCmd_pop(smtlibv2Parser.Cmd_popContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 */
	void exitCmd_pop(smtlibv2Parser.Cmd_popContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 */
	void enterCmd_push(smtlibv2Parser.Cmd_pushContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 */
	void exitCmd_push(smtlibv2Parser.Cmd_pushContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 */
	void enterCmd_reset(smtlibv2Parser.Cmd_resetContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 */
	void exitCmd_reset(smtlibv2Parser.Cmd_resetContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_resetAssertions(smtlibv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_resetAssertions(smtlibv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setInfo(smtlibv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setInfo(smtlibv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setLogic(smtlibv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setLogic(smtlibv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setOption(smtlibv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setOption(smtlibv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterAssert(smtlibv2Parser.AssertContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitAssert(smtlibv2Parser.AssertContext ctx);
	/**
	 * Enter a parse tree produced by the {@code check}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterCheck(smtlibv2Parser.CheckContext ctx);
	/**
	 * Exit a parse tree produced by the {@code check}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitCheck(smtlibv2Parser.CheckContext ctx);
	/**
	 * Enter a parse tree produced by the {@code check_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterCheck_assume(smtlibv2Parser.Check_assumeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code check_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitCheck_assume(smtlibv2Parser.Check_assumeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code decl_const}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDecl_const(smtlibv2Parser.Decl_constContext ctx);
	/**
	 * Exit a parse tree produced by the {@code decl_const}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDecl_const(smtlibv2Parser.Decl_constContext ctx);
	/**
	 * Enter a parse tree produced by the {@code decl_data}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDecl_data(smtlibv2Parser.Decl_dataContext ctx);
	/**
	 * Exit a parse tree produced by the {@code decl_data}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDecl_data(smtlibv2Parser.Decl_dataContext ctx);
	/**
	 * Enter a parse tree produced by the {@code decl_datas}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDecl_datas(smtlibv2Parser.Decl_datasContext ctx);
	/**
	 * Exit a parse tree produced by the {@code decl_datas}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDecl_datas(smtlibv2Parser.Decl_datasContext ctx);
	/**
	 * Enter a parse tree produced by the {@code decl_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDecl_fun(smtlibv2Parser.Decl_funContext ctx);
	/**
	 * Exit a parse tree produced by the {@code decl_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDecl_fun(smtlibv2Parser.Decl_funContext ctx);
	/**
	 * Enter a parse tree produced by the {@code decl_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDecl_sort(smtlibv2Parser.Decl_sortContext ctx);
	/**
	 * Exit a parse tree produced by the {@code decl_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDecl_sort(smtlibv2Parser.Decl_sortContext ctx);
	/**
	 * Enter a parse tree produced by the {@code def_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDef_fun(smtlibv2Parser.Def_funContext ctx);
	/**
	 * Exit a parse tree produced by the {@code def_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDef_fun(smtlibv2Parser.Def_funContext ctx);
	/**
	 * Enter a parse tree produced by the {@code def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDef_fun_rec(smtlibv2Parser.Def_fun_recContext ctx);
	/**
	 * Exit a parse tree produced by the {@code def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDef_fun_rec(smtlibv2Parser.Def_fun_recContext ctx);
	/**
	 * Enter a parse tree produced by the {@code def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDef_funs_rec(smtlibv2Parser.Def_funs_recContext ctx);
	/**
	 * Exit a parse tree produced by the {@code def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDef_funs_rec(smtlibv2Parser.Def_funs_recContext ctx);
	/**
	 * Enter a parse tree produced by the {@code def_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterDef_sort(smtlibv2Parser.Def_sortContext ctx);
	/**
	 * Exit a parse tree produced by the {@code def_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitDef_sort(smtlibv2Parser.Def_sortContext ctx);
	/**
	 * Enter a parse tree produced by the {@code echo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterEcho(smtlibv2Parser.EchoContext ctx);
	/**
	 * Exit a parse tree produced by the {@code echo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitEcho(smtlibv2Parser.EchoContext ctx);
	/**
	 * Enter a parse tree produced by the {@code exit}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterExit(smtlibv2Parser.ExitContext ctx);
	/**
	 * Exit a parse tree produced by the {@code exit}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitExit(smtlibv2Parser.ExitContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_assert(smtlibv2Parser.Get_assertContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_assert(smtlibv2Parser.Get_assertContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_assign}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_assign(smtlibv2Parser.Get_assignContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_assign}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_assign(smtlibv2Parser.Get_assignContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_info}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_info(smtlibv2Parser.Get_infoContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_info}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_info(smtlibv2Parser.Get_infoContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_model}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_model(smtlibv2Parser.Get_modelContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_model}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_model(smtlibv2Parser.Get_modelContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_option(smtlibv2Parser.Get_optionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_option(smtlibv2Parser.Get_optionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_proof}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_proof(smtlibv2Parser.Get_proofContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_proof}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_proof(smtlibv2Parser.Get_proofContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_assume(smtlibv2Parser.Get_unsat_assumeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_assume(smtlibv2Parser.Get_unsat_assumeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_core(smtlibv2Parser.Get_unsat_coreContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_core(smtlibv2Parser.Get_unsat_coreContext ctx);
	/**
	 * Enter a parse tree produced by the {@code get_val}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterGet_val(smtlibv2Parser.Get_valContext ctx);
	/**
	 * Exit a parse tree produced by the {@code get_val}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitGet_val(smtlibv2Parser.Get_valContext ctx);
	/**
	 * Enter a parse tree produced by the {@code pop}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterPop(smtlibv2Parser.PopContext ctx);
	/**
	 * Exit a parse tree produced by the {@code pop}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitPop(smtlibv2Parser.PopContext ctx);
	/**
	 * Enter a parse tree produced by the {@code push}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterPush(smtlibv2Parser.PushContext ctx);
	/**
	 * Exit a parse tree produced by the {@code push}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitPush(smtlibv2Parser.PushContext ctx);
	/**
	 * Enter a parse tree produced by the {@code reset}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterReset(smtlibv2Parser.ResetContext ctx);
	/**
	 * Exit a parse tree produced by the {@code reset}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitReset(smtlibv2Parser.ResetContext ctx);
	/**
	 * Enter a parse tree produced by the {@code reset_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterReset_assert(smtlibv2Parser.Reset_assertContext ctx);
	/**
	 * Exit a parse tree produced by the {@code reset_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitReset_assert(smtlibv2Parser.Reset_assertContext ctx);
	/**
	 * Enter a parse tree produced by the {@code setInfo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterSetInfo(smtlibv2Parser.SetInfoContext ctx);
	/**
	 * Exit a parse tree produced by the {@code setInfo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitSetInfo(smtlibv2Parser.SetInfoContext ctx);
	/**
	 * Enter a parse tree produced by the {@code set_logic}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterSet_logic(smtlibv2Parser.Set_logicContext ctx);
	/**
	 * Exit a parse tree produced by the {@code set_logic}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitSet_logic(smtlibv2Parser.Set_logicContext ctx);
	/**
	 * Enter a parse tree produced by the {@code set_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterSet_option(smtlibv2Parser.Set_optionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code set_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitSet_option(smtlibv2Parser.Set_optionContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#b_value}.
	 * @param ctx the parse tree
	 */
	void enterB_value(smtlibv2Parser.B_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#b_value}.
	 * @param ctx the parse tree
	 */
	void exitB_value(smtlibv2Parser.B_valueContext ctx);
	/**
	 * Enter a parse tree produced by the {@code diagnose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterDiagnose(smtlibv2Parser.DiagnoseContext ctx);
	/**
	 * Exit a parse tree produced by the {@code diagnose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitDiagnose(smtlibv2Parser.DiagnoseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code global}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterGlobal(smtlibv2Parser.GlobalContext ctx);
	/**
	 * Exit a parse tree produced by the {@code global}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitGlobal(smtlibv2Parser.GlobalContext ctx);
	/**
	 * Enter a parse tree produced by the {@code interactive}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterInteractive(smtlibv2Parser.InteractiveContext ctx);
	/**
	 * Exit a parse tree produced by the {@code interactive}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitInteractive(smtlibv2Parser.InteractiveContext ctx);
	/**
	 * Enter a parse tree produced by the {@code print_succ}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterPrint_succ(smtlibv2Parser.Print_succContext ctx);
	/**
	 * Exit a parse tree produced by the {@code print_succ}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitPrint_succ(smtlibv2Parser.Print_succContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_assert}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_assert(smtlibv2Parser.Prod_assertContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_assert}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_assert(smtlibv2Parser.Prod_assertContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_assign}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_assign(smtlibv2Parser.Prod_assignContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_assign}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_assign(smtlibv2Parser.Prod_assignContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_mod}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_mod(smtlibv2Parser.Prod_modContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_mod}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_mod(smtlibv2Parser.Prod_modContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_proofs}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_proofs(smtlibv2Parser.Prod_proofsContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_proofs}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_proofs(smtlibv2Parser.Prod_proofsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_unsat_assume(smtlibv2Parser.Prod_unsat_assumeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_unsat_assume(smtlibv2Parser.Prod_unsat_assumeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code prod_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterProd_unsat_core(smtlibv2Parser.Prod_unsat_coreContext ctx);
	/**
	 * Exit a parse tree produced by the {@code prod_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitProd_unsat_core(smtlibv2Parser.Prod_unsat_coreContext ctx);
	/**
	 * Enter a parse tree produced by the {@code rand_seed}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterRand_seed(smtlibv2Parser.Rand_seedContext ctx);
	/**
	 * Exit a parse tree produced by the {@code rand_seed}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitRand_seed(smtlibv2Parser.Rand_seedContext ctx);
	/**
	 * Enter a parse tree produced by the {@code reg_out}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterReg_out(smtlibv2Parser.Reg_outContext ctx);
	/**
	 * Exit a parse tree produced by the {@code reg_out}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitReg_out(smtlibv2Parser.Reg_outContext ctx);
	/**
	 * Enter a parse tree produced by the {@code repro}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterRepro(smtlibv2Parser.ReproContext ctx);
	/**
	 * Exit a parse tree produced by the {@code repro}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitRepro(smtlibv2Parser.ReproContext ctx);
	/**
	 * Enter a parse tree produced by the {@code verbose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterVerbose(smtlibv2Parser.VerboseContext ctx);
	/**
	 * Exit a parse tree produced by the {@code verbose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitVerbose(smtlibv2Parser.VerboseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code opt_attr}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterOpt_attr(smtlibv2Parser.Opt_attrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code opt_attr}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitOpt_attr(smtlibv2Parser.Opt_attrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code all_stat}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterAll_stat(smtlibv2Parser.All_statContext ctx);
	/**
	 * Exit a parse tree produced by the {@code all_stat}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitAll_stat(smtlibv2Parser.All_statContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterAssert_stack(smtlibv2Parser.Assert_stackContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitAssert_stack(smtlibv2Parser.Assert_stackContext ctx);
	/**
	 * Enter a parse tree produced by the {@code authors}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterAuthors(smtlibv2Parser.AuthorsContext ctx);
	/**
	 * Exit a parse tree produced by the {@code authors}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitAuthors(smtlibv2Parser.AuthorsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code error}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterError(smtlibv2Parser.ErrorContext ctx);
	/**
	 * Exit a parse tree produced by the {@code error}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitError(smtlibv2Parser.ErrorContext ctx);
	/**
	 * Enter a parse tree produced by the {@code name}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterName(smtlibv2Parser.NameContext ctx);
	/**
	 * Exit a parse tree produced by the {@code name}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitName(smtlibv2Parser.NameContext ctx);
	/**
	 * Enter a parse tree produced by the {@code r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterR_unknown(smtlibv2Parser.R_unknownContext ctx);
	/**
	 * Exit a parse tree produced by the {@code r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitR_unknown(smtlibv2Parser.R_unknownContext ctx);
	/**
	 * Enter a parse tree produced by the {@code version}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterVersion(smtlibv2Parser.VersionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code version}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitVersion(smtlibv2Parser.VersionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_key}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterInfo_key(smtlibv2Parser.Info_keyContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_key}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitInfo_key(smtlibv2Parser.Info_keyContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 */
	void enterError_behaviour(smtlibv2Parser.Error_behaviourContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 */
	void exitError_behaviour(smtlibv2Parser.Error_behaviourContext ctx);
	/**
	 * Enter a parse tree produced by the {@code memout}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void enterMemout(smtlibv2Parser.MemoutContext ctx);
	/**
	 * Exit a parse tree produced by the {@code memout}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void exitMemout(smtlibv2Parser.MemoutContext ctx);
	/**
	 * Enter a parse tree produced by the {@code incomp}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void enterIncomp(smtlibv2Parser.IncompContext ctx);
	/**
	 * Exit a parse tree produced by the {@code incomp}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void exitIncomp(smtlibv2Parser.IncompContext ctx);
	/**
	 * Enter a parse tree produced by the {@code r_unnown_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void enterR_unnown_s_expr(smtlibv2Parser.R_unnown_s_exprContext ctx);
	/**
	 * Exit a parse tree produced by the {@code r_unnown_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void exitR_unnown_s_expr(smtlibv2Parser.R_unnown_s_exprContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_def_fun}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_def_fun(smtlibv2Parser.Resp_def_funContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_def_fun}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_def_fun(smtlibv2Parser.Resp_def_funContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_def_fun_rec(smtlibv2Parser.Resp_def_fun_recContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_def_fun_rec(smtlibv2Parser.Resp_def_fun_recContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_def_funs_rec(smtlibv2Parser.Resp_def_funs_recContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_def_funs_rec(smtlibv2Parser.Resp_def_funs_recContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_assert_stack(smtlibv2Parser.Info_assert_stackContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_assert_stack(smtlibv2Parser.Info_assert_stackContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_authors}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_authors(smtlibv2Parser.Info_authorsContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_authors}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_authors(smtlibv2Parser.Info_authorsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_error}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_error(smtlibv2Parser.Info_errorContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_error}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_error(smtlibv2Parser.Info_errorContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_name}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_name(smtlibv2Parser.Info_nameContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_name}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_name(smtlibv2Parser.Info_nameContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_r_unknown(smtlibv2Parser.Info_r_unknownContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_r_unknown(smtlibv2Parser.Info_r_unknownContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_version}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_version(smtlibv2Parser.Info_versionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_version}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_version(smtlibv2Parser.Info_versionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code info_attr}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_attr(smtlibv2Parser.Info_attrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code info_attr}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_attr(smtlibv2Parser.Info_attrContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 */
	void enterValuation_pair(smtlibv2Parser.Valuation_pairContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 */
	void exitValuation_pair(smtlibv2Parser.Valuation_pairContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 */
	void enterT_valuation_pair(smtlibv2Parser.T_valuation_pairContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 */
	void exitT_valuation_pair(smtlibv2Parser.T_valuation_pairContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 */
	void enterCheck_sat_response(smtlibv2Parser.Check_sat_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 */
	void exitCheck_sat_response(smtlibv2Parser.Check_sat_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#echo_response}.
	 * @param ctx the parse tree
	 */
	void enterEcho_response(smtlibv2Parser.Echo_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#echo_response}.
	 * @param ctx the parse tree
	 */
	void exitEcho_response(smtlibv2Parser.Echo_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_assertions_response(smtlibv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_assertions_response(smtlibv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_assignment_response(smtlibv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_assignment_response(smtlibv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_info_response(smtlibv2Parser.Get_info_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_info_response(smtlibv2Parser.Get_info_responseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code rs_model}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void enterRs_model(smtlibv2Parser.Rs_modelContext ctx);
	/**
	 * Exit a parse tree produced by the {@code rs_model}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void exitRs_model(smtlibv2Parser.Rs_modelContext ctx);
	/**
	 * Enter a parse tree produced by the {@code model_resp}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void enterModel_resp(smtlibv2Parser.Model_respContext ctx);
	/**
	 * Exit a parse tree produced by the {@code model_resp}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void exitModel_resp(smtlibv2Parser.Model_respContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_option_response(smtlibv2Parser.Get_option_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_option_response(smtlibv2Parser.Get_option_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_proof_response(smtlibv2Parser.Get_proof_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_proof_response(smtlibv2Parser.Get_proof_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_assump_response(smtlibv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_assump_response(smtlibv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_core_response(smtlibv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_core_response(smtlibv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_value_response(smtlibv2Parser.Get_value_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_value_response(smtlibv2Parser.Get_value_responseContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_check_sat}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_check_sat(smtlibv2Parser.Resp_check_satContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_check_sat}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_check_sat(smtlibv2Parser.Resp_check_satContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_echo}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_echo(smtlibv2Parser.Resp_echoContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_echo}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_echo(smtlibv2Parser.Resp_echoContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_get_assert}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_get_assert(smtlibv2Parser.Resp_get_assertContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_get_assert}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_get_assert(smtlibv2Parser.Resp_get_assertContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_gett_assign}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_gett_assign(smtlibv2Parser.Resp_gett_assignContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_gett_assign}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_gett_assign(smtlibv2Parser.Resp_gett_assignContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_get_info}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_get_info(smtlibv2Parser.Resp_get_infoContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_get_info}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_get_info(smtlibv2Parser.Resp_get_infoContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_get_model}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_get_model(smtlibv2Parser.Resp_get_modelContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_get_model}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_get_model(smtlibv2Parser.Resp_get_modelContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_option}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_option(smtlibv2Parser.Resp_optionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_option}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_option(smtlibv2Parser.Resp_optionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_proof}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_proof(smtlibv2Parser.Resp_proofContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_proof}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_proof(smtlibv2Parser.Resp_proofContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_unsat_assume(smtlibv2Parser.Resp_unsat_assumeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_unsat_assume(smtlibv2Parser.Resp_unsat_assumeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_unsat_core(smtlibv2Parser.Resp_unsat_coreContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_unsat_core(smtlibv2Parser.Resp_unsat_coreContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_value}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_value(smtlibv2Parser.Resp_valueContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_value}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_value(smtlibv2Parser.Resp_valueContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_success}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_success(smtlibv2Parser.Resp_successContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_success}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_success(smtlibv2Parser.Resp_successContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_spec_successs}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_spec_successs(smtlibv2Parser.Resp_spec_successsContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_spec_successs}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_spec_successs(smtlibv2Parser.Resp_spec_successsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_unsupported}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_unsupported(smtlibv2Parser.Resp_unsupportedContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_unsupported}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_unsupported(smtlibv2Parser.Resp_unsupportedContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resp_error}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterResp_error(smtlibv2Parser.Resp_errorContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resp_error}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitResp_error(smtlibv2Parser.Resp_errorContext ctx);
}