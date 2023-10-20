// Generated from /home/janel/Desktop/Studium/Semester_6/Bachelorarbeit/nochmalneu/src/org/sosy_lab/java_smt/utils/Parsers/smtlibv2.g4 by ANTLR 4.13.1
package org.sosy_lab.java_smt.utils.Parsers;
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart(smtlibv2Parser.StartContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimpleSymbol(smtlibv2Parser.SimpleSymbolContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSymbol(smtlibv2Parser.SymbolContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitKeyword(smtlibv2Parser.KeywordContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant(smtlibv2Parser.Spec_constantContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_expr(smtlibv2Parser.S_exprContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIndex(smtlibv2Parser.IndexContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdentifier(smtlibv2Parser.IdentifierContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribute_value(smtlibv2Parser.Attribute_valueContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribute(smtlibv2Parser.AttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort(smtlibv2Parser.SortContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQual_identifer(smtlibv2Parser.Qual_identiferContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPattern(smtlibv2Parser.PatternContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#match_case}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMatch_case(smtlibv2Parser.Match_caseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm(smtlibv2Parser.TermContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFun_symbol_decl(smtlibv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPar_fun_symbol_decl(smtlibv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_attribute(smtlibv2Parser.Theory_attributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_decl(smtlibv2Parser.Theory_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_attribue(smtlibv2Parser.Logic_attribueContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDatatype_dec(smtlibv2Parser.Datatype_decContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProp_literal(smtlibv2Parser.Prop_literalContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCommand(smtlibv2Parser.CommandContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#b_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitB_value(smtlibv2Parser.B_valueContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOption(smtlibv2Parser.OptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_flag(smtlibv2Parser.Info_flagContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitError_behaviour(smtlibv2Parser.Error_behaviourContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReason_unknown(smtlibv2Parser.Reason_unknownContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModel_response(smtlibv2Parser.Model_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_response(smtlibv2Parser.Info_responseContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_model_response(smtlibv2Parser.Get_model_responseContext ctx);
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
	 * Visit a parse tree produced by {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpecific_success_response(smtlibv2Parser.Specific_success_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneral_response(smtlibv2Parser.General_responseContext ctx);
}