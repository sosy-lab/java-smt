// Generated from /home/dalux/Dokumente/IdeaProjects/java-smt/src/org/sosy_lab/java_smt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link smtlibv2Parser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface smtlibv2Visitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by the {@code start_logic}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart_logic(smtlibv2Parser.Start_logicContext ctx);
	/**
	 * Visit a parse tree produced by the {@code start_theory}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart_theory(smtlibv2Parser.Start_theoryContext ctx);
	/**
	 * Visit a parse tree produced by the {@code start_script}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart_script(smtlibv2Parser.Start_scriptContext ctx);
	/**
	 * Visit a parse tree produced by the {@code start_gen_resp}
	 * labeled alternative in {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart_gen_resp(smtlibv2Parser.Start_gen_respContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Visit a parse tree produced by the {@code simp_pre_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimp_pre_symb(smtlibv2Parser.Simp_pre_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code simp_undef_symb}
	 * labeled alternative in {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimp_undef_symb(smtlibv2Parser.Simp_undef_symbContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuotedSymbol(smtlibv2Parser.QuotedSymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPredefSymbol(smtlibv2Parser.PredefSymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPredefKeyword(smtlibv2Parser.PredefKeywordContext ctx);
	/**
	 * Visit a parse tree produced by the {@code simpsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimpsymb(smtlibv2Parser.SimpsymbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code quotsymb}
	 * labeled alternative in {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuotsymb(smtlibv2Parser.QuotsymbContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#numeral}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumeral(smtlibv2Parser.NumeralContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#decimal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecimal(smtlibv2Parser.DecimalContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHexadecimal(smtlibv2Parser.HexadecimalContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#binary}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinary(smtlibv2Parser.BinaryContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#string}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitString(smtlibv2Parser.StringContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floatingpoint}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloatingpoint(smtlibv2Parser.FloatingpointContext ctx);
	/**
	 * Visit a parse tree produced by the {@code pre_key}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPre_key(smtlibv2Parser.Pre_keyContext ctx);
	/**
	 * Visit a parse tree produced by the {@code key_simsymb}
	 * labeled alternative in {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitKey_simsymb(smtlibv2Parser.Key_simsymbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_num}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_num(smtlibv2Parser.Spec_constant_numContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_dec}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_dec(smtlibv2Parser.Spec_constant_decContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_hex}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_hex(smtlibv2Parser.Spec_constant_hexContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_bin}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_bin(smtlibv2Parser.Spec_constant_binContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_string}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_string(smtlibv2Parser.Spec_constant_stringContext ctx);
	/**
	 * Visit a parse tree produced by the {@code spec_constant_floating_point}
	 * labeled alternative in {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant_floating_point(smtlibv2Parser.Spec_constant_floating_pointContext ctx);
	/**
	 * Visit a parse tree produced by the {@code s_expr_spec}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_expr_spec(smtlibv2Parser.S_expr_specContext ctx);
	/**
	 * Visit a parse tree produced by the {@code s_expr_symb}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_expr_symb(smtlibv2Parser.S_expr_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code s_expr_key}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_expr_key(smtlibv2Parser.S_expr_keyContext ctx);
	/**
	 * Visit a parse tree produced by the {@code multi_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMulti_s_expr(smtlibv2Parser.Multi_s_exprContext ctx);
	/**
	 * Visit a parse tree produced by the {@code idx_num}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdx_num(smtlibv2Parser.Idx_numContext ctx);
	/**
	 * Visit a parse tree produced by the {@code idx_symb}
	 * labeled alternative in {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdx_symb(smtlibv2Parser.Idx_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code id_symb}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitId_symb(smtlibv2Parser.Id_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code id_symb_idx}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitId_symb_idx(smtlibv2Parser.Id_symb_idxContext ctx);
	/**
	 * Visit a parse tree produced by the {@code id_fp}
	 * labeled alternative in {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitId_fp(smtlibv2Parser.Id_fpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code attr_spec}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttr_spec(smtlibv2Parser.Attr_specContext ctx);
	/**
	 * Visit a parse tree produced by the {@code attr_symb}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttr_symb(smtlibv2Parser.Attr_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code attr_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttr_s_expr(smtlibv2Parser.Attr_s_exprContext ctx);
	/**
	 * Visit a parse tree produced by the {@code attr_key}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttr_key(smtlibv2Parser.Attr_keyContext ctx);
	/**
	 * Visit a parse tree produced by the {@code attr_key_attr}
	 * labeled alternative in {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttr_key_attr(smtlibv2Parser.Attr_key_attrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code sort_id}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort_id(smtlibv2Parser.Sort_idContext ctx);
	/**
	 * Visit a parse tree produced by the {@code multisort}
	 * labeled alternative in {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultisort(smtlibv2Parser.MultisortContext ctx);
	/**
	 * Visit a parse tree produced by the {@code qual_id}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQual_id(smtlibv2Parser.Qual_idContext ctx);
	/**
	 * Visit a parse tree produced by the {@code qual_id_sort}
	 * labeled alternative in {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQual_id_sort(smtlibv2Parser.Qual_id_sortContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#var_binding}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVar_binding(smtlibv2Parser.Var_bindingContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSorted_var(smtlibv2Parser.Sorted_varContext ctx);
	/**
	 * Visit a parse tree produced by the {@code pattern_symb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPattern_symb(smtlibv2Parser.Pattern_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code pattern_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPattern_multisymb(smtlibv2Parser.Pattern_multisymbContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#match_case}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMatch_case(smtlibv2Parser.Match_caseContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_spec_const}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_spec_const(smtlibv2Parser.Term_spec_constContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_qual_id}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_qual_id(smtlibv2Parser.Term_qual_idContext ctx);
	/**
	 * Visit a parse tree produced by the {@code multiterm}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiterm(smtlibv2Parser.MultitermContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_let}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_let(smtlibv2Parser.Term_letContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_forall}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_forall(smtlibv2Parser.Term_forallContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_exists}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_exists(smtlibv2Parser.Term_existsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_match}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_match(smtlibv2Parser.Term_matchContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_exclam}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_exclam(smtlibv2Parser.Term_exclamContext ctx);
	/**
	 * Visit a parse tree produced by the {@code term_floating_point}
	 * labeled alternative in {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm_floating_point(smtlibv2Parser.Term_floating_pointContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_abs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_abs(smtlibv2Parser.Fp_absContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_neg}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_neg(smtlibv2Parser.Fp_negContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_add}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_add(smtlibv2Parser.Fp_addContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_sub}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_sub(smtlibv2Parser.Fp_subContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_mul}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_mul(smtlibv2Parser.Fp_mulContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_div}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_div(smtlibv2Parser.Fp_divContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_fma}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_fma(smtlibv2Parser.Fp_fmaContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_sqrt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_sqrt(smtlibv2Parser.Fp_sqrtContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_rem}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_rem(smtlibv2Parser.Fp_remContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_roundToIntegral}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_roundToIntegral(smtlibv2Parser.Fp_roundToIntegralContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_min}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_min(smtlibv2Parser.Fp_minContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_max}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_max(smtlibv2Parser.Fp_maxContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_leq}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_leq(smtlibv2Parser.Fp_leqContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_lt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_lt(smtlibv2Parser.Fp_ltContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_geq}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_geq(smtlibv2Parser.Fp_geqContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_gt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_gt(smtlibv2Parser.Fp_gtContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_eq}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_eq(smtlibv2Parser.Fp_eqContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isNormal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isNormal(smtlibv2Parser.Fp_isNormalContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isSubnormal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isSubnormal(smtlibv2Parser.Fp_isSubnormalContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isZero}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isZero(smtlibv2Parser.Fp_isZeroContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isInfinite}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isInfinite(smtlibv2Parser.Fp_isInfiniteContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isNegative}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isNegative(smtlibv2Parser.Fp_isNegativeContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#fp_isPositive}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFp_isPositive(smtlibv2Parser.Fp_isPositiveContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_point_operator_with_1_input}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_point_operator_with_1_input(smtlibv2Parser.Floating_point_operator_with_1_inputContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_point_operator_with_2_inputs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_point_operator_with_2_inputs(smtlibv2Parser.Floating_point_operator_with_2_inputsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_points_with_RM_1_input}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_points_with_RM_1_input(smtlibv2Parser.Floating_points_with_RM_1_inputContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_points_with_RM_2_inputs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_points_with_RM_2_inputs(smtlibv2Parser.Floating_points_with_RM_2_inputsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_point_funs_with_RM_3_inputs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_point_funs_with_RM_3_inputs(smtlibv2Parser.Floating_point_funs_with_RM_3_inputsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_point_operations}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_point_operations(smtlibv2Parser.Floating_point_operationsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#floating_point_conversions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloating_point_conversions(smtlibv2Parser.Floating_point_conversionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#to_fp_input}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTo_fp_input(smtlibv2Parser.To_fp_inputContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#to_fp_operations}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTo_fp_operations(smtlibv2Parser.To_fp_operationsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#from_fp_operations}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFrom_fp_operations(smtlibv2Parser.From_fp_operationsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort_symbol_decl(smtlibv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMeta_spec_constant(smtlibv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Visit a parse tree produced by the {@code fun_symb_spec}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFun_symb_spec(smtlibv2Parser.Fun_symb_specContext ctx);
	/**
	 * Visit a parse tree produced by the {@code fun_symb_meta}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFun_symb_meta(smtlibv2Parser.Fun_symb_metaContext ctx);
	/**
	 * Visit a parse tree produced by the {@code fun_symb_id}
	 * labeled alternative in {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFun_symb_id(smtlibv2Parser.Fun_symb_idContext ctx);
	/**
	 * Visit a parse tree produced by the {@code par_fun_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPar_fun_symb(smtlibv2Parser.Par_fun_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code par_fun_multi_symb}
	 * labeled alternative in {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPar_fun_multi_symb(smtlibv2Parser.Par_fun_multi_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_sort}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_sort(smtlibv2Parser.Theory_sortContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_fun}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_fun(smtlibv2Parser.Theory_funContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_sort_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_sort_descr(smtlibv2Parser.Theory_sort_descrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_fun_descr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_fun_descr(smtlibv2Parser.Theory_fun_descrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_def}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_def(smtlibv2Parser.Theory_defContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_val}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_val(smtlibv2Parser.Theory_valContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_notes}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_notes(smtlibv2Parser.Theory_notesContext ctx);
	/**
	 * Visit a parse tree produced by the {@code theory_attr}
	 * labeled alternative in {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_attr(smtlibv2Parser.Theory_attrContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_decl(smtlibv2Parser.Theory_declContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_theory}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_theory(smtlibv2Parser.Logic_theoryContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_language}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_language(smtlibv2Parser.Logic_languageContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_ext}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_ext(smtlibv2Parser.Logic_extContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_val}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_val(smtlibv2Parser.Logic_valContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_notes}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_notes(smtlibv2Parser.Logic_notesContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logic_attr}
	 * labeled alternative in {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_attr(smtlibv2Parser.Logic_attrContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#logic}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic(smtlibv2Parser.LogicContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort_dec(smtlibv2Parser.Sort_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSelector_dec(smtlibv2Parser.Selector_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstructor_dec(smtlibv2Parser.Constructor_decContext ctx);
	/**
	 * Visit a parse tree produced by the {@code data_constr}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitData_constr(smtlibv2Parser.Data_constrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code data_multisymb}
	 * labeled alternative in {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitData_multisymb(smtlibv2Parser.Data_multisymbContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#function_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunction_dec(smtlibv2Parser.Function_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#function_def}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunction_def(smtlibv2Parser.Function_defContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prop_symb}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProp_symb(smtlibv2Parser.Prop_symbContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prop_not}
	 * labeled alternative in {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProp_not(smtlibv2Parser.Prop_notContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#script}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitScript(smtlibv2Parser.ScriptContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_assert(smtlibv2Parser.Cmd_assertContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_checkSat(smtlibv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_checkSatAssuming(smtlibv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareConst(smtlibv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareDatatype(smtlibv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareDatatypes(smtlibv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareFun(smtlibv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareSort(smtlibv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFun(smtlibv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFunRec(smtlibv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFunsRec(smtlibv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineSort(smtlibv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_echo(smtlibv2Parser.Cmd_echoContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_exit(smtlibv2Parser.Cmd_exitContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getAssertions(smtlibv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getAssignment(smtlibv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getInfo(smtlibv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getModel(smtlibv2Parser.Cmd_getModelContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getOption(smtlibv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getProof(smtlibv2Parser.Cmd_getProofContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getUnsatAssumptions(smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getUnsatCore(smtlibv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getValue(smtlibv2Parser.Cmd_getValueContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_pop(smtlibv2Parser.Cmd_popContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_push(smtlibv2Parser.Cmd_pushContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_reset(smtlibv2Parser.Cmd_resetContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_resetAssertions(smtlibv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setInfo(smtlibv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setLogic(smtlibv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setOption(smtlibv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssert(smtlibv2Parser.AssertContext ctx);
	/**
	 * Visit a parse tree produced by the {@code check}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCheck(smtlibv2Parser.CheckContext ctx);
	/**
	 * Visit a parse tree produced by the {@code check_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCheck_assume(smtlibv2Parser.Check_assumeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code decl_const}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl_const(smtlibv2Parser.Decl_constContext ctx);
	/**
	 * Visit a parse tree produced by the {@code decl_data}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl_data(smtlibv2Parser.Decl_dataContext ctx);
	/**
	 * Visit a parse tree produced by the {@code decl_datas}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl_datas(smtlibv2Parser.Decl_datasContext ctx);
	/**
	 * Visit a parse tree produced by the {@code decl_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl_fun(smtlibv2Parser.Decl_funContext ctx);
	/**
	 * Visit a parse tree produced by the {@code decl_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl_sort(smtlibv2Parser.Decl_sortContext ctx);
	/**
	 * Visit a parse tree produced by the {@code def_fun}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDef_fun(smtlibv2Parser.Def_funContext ctx);
	/**
	 * Visit a parse tree produced by the {@code def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDef_fun_rec(smtlibv2Parser.Def_fun_recContext ctx);
	/**
	 * Visit a parse tree produced by the {@code def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDef_funs_rec(smtlibv2Parser.Def_funs_recContext ctx);
	/**
	 * Visit a parse tree produced by the {@code def_sort}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDef_sort(smtlibv2Parser.Def_sortContext ctx);
	/**
	 * Visit a parse tree produced by the {@code echo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEcho(smtlibv2Parser.EchoContext ctx);
	/**
	 * Visit a parse tree produced by the {@code exit}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExit(smtlibv2Parser.ExitContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assert(smtlibv2Parser.Get_assertContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_assign}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assign(smtlibv2Parser.Get_assignContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_info}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_info(smtlibv2Parser.Get_infoContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_model}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_model(smtlibv2Parser.Get_modelContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_option(smtlibv2Parser.Get_optionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_proof}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_proof(smtlibv2Parser.Get_proofContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_assume(smtlibv2Parser.Get_unsat_assumeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_core(smtlibv2Parser.Get_unsat_coreContext ctx);
	/**
	 * Visit a parse tree produced by the {@code get_val}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_val(smtlibv2Parser.Get_valContext ctx);
	/**
	 * Visit a parse tree produced by the {@code pop}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPop(smtlibv2Parser.PopContext ctx);
	/**
	 * Visit a parse tree produced by the {@code push}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPush(smtlibv2Parser.PushContext ctx);
	/**
	 * Visit a parse tree produced by the {@code reset}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReset(smtlibv2Parser.ResetContext ctx);
	/**
	 * Visit a parse tree produced by the {@code reset_assert}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReset_assert(smtlibv2Parser.Reset_assertContext ctx);
	/**
	 * Visit a parse tree produced by the {@code setInfo}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSetInfo(smtlibv2Parser.SetInfoContext ctx);
	/**
	 * Visit a parse tree produced by the {@code set_logic}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSet_logic(smtlibv2Parser.Set_logicContext ctx);
	/**
	 * Visit a parse tree produced by the {@code set_option}
	 * labeled alternative in {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSet_option(smtlibv2Parser.Set_optionContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#b_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitB_value(smtlibv2Parser.B_valueContext ctx);
	/**
	 * Visit a parse tree produced by the {@code diagnose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDiagnose(smtlibv2Parser.DiagnoseContext ctx);
	/**
	 * Visit a parse tree produced by the {@code global}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGlobal(smtlibv2Parser.GlobalContext ctx);
	/**
	 * Visit a parse tree produced by the {@code interactive}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInteractive(smtlibv2Parser.InteractiveContext ctx);
	/**
	 * Visit a parse tree produced by the {@code print_succ}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrint_succ(smtlibv2Parser.Print_succContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_assert}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_assert(smtlibv2Parser.Prod_assertContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_assign}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_assign(smtlibv2Parser.Prod_assignContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_mod}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_mod(smtlibv2Parser.Prod_modContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_proofs}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_proofs(smtlibv2Parser.Prod_proofsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_unsat_assume(smtlibv2Parser.Prod_unsat_assumeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prod_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProd_unsat_core(smtlibv2Parser.Prod_unsat_coreContext ctx);
	/**
	 * Visit a parse tree produced by the {@code rand_seed}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRand_seed(smtlibv2Parser.Rand_seedContext ctx);
	/**
	 * Visit a parse tree produced by the {@code reg_out}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReg_out(smtlibv2Parser.Reg_outContext ctx);
	/**
	 * Visit a parse tree produced by the {@code repro}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRepro(smtlibv2Parser.ReproContext ctx);
	/**
	 * Visit a parse tree produced by the {@code verbose}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVerbose(smtlibv2Parser.VerboseContext ctx);
	/**
	 * Visit a parse tree produced by the {@code opt_attr}
	 * labeled alternative in {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOpt_attr(smtlibv2Parser.Opt_attrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code all_stat}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAll_stat(smtlibv2Parser.All_statContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssert_stack(smtlibv2Parser.Assert_stackContext ctx);
	/**
	 * Visit a parse tree produced by the {@code authors}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAuthors(smtlibv2Parser.AuthorsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code error}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitError(smtlibv2Parser.ErrorContext ctx);
	/**
	 * Visit a parse tree produced by the {@code name}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitName(smtlibv2Parser.NameContext ctx);
	/**
	 * Visit a parse tree produced by the {@code r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitR_unknown(smtlibv2Parser.R_unknownContext ctx);
	/**
	 * Visit a parse tree produced by the {@code version}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVersion(smtlibv2Parser.VersionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_key}
	 * labeled alternative in {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_key(smtlibv2Parser.Info_keyContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitError_behaviour(smtlibv2Parser.Error_behaviourContext ctx);
	/**
	 * Visit a parse tree produced by the {@code memout}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMemout(smtlibv2Parser.MemoutContext ctx);
	/**
	 * Visit a parse tree produced by the {@code incomp}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIncomp(smtlibv2Parser.IncompContext ctx);
	/**
	 * Visit a parse tree produced by the {@code r_unnown_s_expr}
	 * labeled alternative in {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitR_unnown_s_expr(smtlibv2Parser.R_unnown_s_exprContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_def_fun}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_def_fun(smtlibv2Parser.Resp_def_funContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_def_fun_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_def_fun_rec(smtlibv2Parser.Resp_def_fun_recContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_def_funs_rec}
	 * labeled alternative in {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_def_funs_rec(smtlibv2Parser.Resp_def_funs_recContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_assert_stack}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_assert_stack(smtlibv2Parser.Info_assert_stackContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_authors}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_authors(smtlibv2Parser.Info_authorsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_error}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_error(smtlibv2Parser.Info_errorContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_name}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_name(smtlibv2Parser.Info_nameContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_r_unknown}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_r_unknown(smtlibv2Parser.Info_r_unknownContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_version}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_version(smtlibv2Parser.Info_versionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code info_attr}
	 * labeled alternative in {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_attr(smtlibv2Parser.Info_attrContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitValuation_pair(smtlibv2Parser.Valuation_pairContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitT_valuation_pair(smtlibv2Parser.T_valuation_pairContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCheck_sat_response(smtlibv2Parser.Check_sat_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#echo_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEcho_response(smtlibv2Parser.Echo_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assertions_response(smtlibv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assignment_response(smtlibv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_info_response(smtlibv2Parser.Get_info_responseContext ctx);
	/**
	 * Visit a parse tree produced by the {@code rs_model}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRs_model(smtlibv2Parser.Rs_modelContext ctx);
	/**
	 * Visit a parse tree produced by the {@code model_resp}
	 * labeled alternative in {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModel_resp(smtlibv2Parser.Model_respContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_option_response(smtlibv2Parser.Get_option_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_proof_response(smtlibv2Parser.Get_proof_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_assump_response(smtlibv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_core_response(smtlibv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_value_response(smtlibv2Parser.Get_value_responseContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_check_sat}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_check_sat(smtlibv2Parser.Resp_check_satContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_echo}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_echo(smtlibv2Parser.Resp_echoContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_get_assert}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_get_assert(smtlibv2Parser.Resp_get_assertContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_gett_assign}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_gett_assign(smtlibv2Parser.Resp_gett_assignContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_get_info}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_get_info(smtlibv2Parser.Resp_get_infoContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_get_model}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_get_model(smtlibv2Parser.Resp_get_modelContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_option}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_option(smtlibv2Parser.Resp_optionContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_proof}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_proof(smtlibv2Parser.Resp_proofContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_unsat_assume}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_unsat_assume(smtlibv2Parser.Resp_unsat_assumeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_unsat_core}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_unsat_core(smtlibv2Parser.Resp_unsat_coreContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_value}
	 * labeled alternative in {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_value(smtlibv2Parser.Resp_valueContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_success}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_success(smtlibv2Parser.Resp_successContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_spec_successs}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_spec_successs(smtlibv2Parser.Resp_spec_successsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_unsupported}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_unsupported(smtlibv2Parser.Resp_unsupportedContext ctx);
	/**
	 * Visit a parse tree produced by the {@code resp_error}
	 * labeled alternative in {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResp_error(smtlibv2Parser.Resp_errorContext ctx);
}