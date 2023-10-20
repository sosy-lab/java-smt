// Generated from /home/janel/Desktop/Studium/Semester_6/Bachelorarbeit/nochmalneu/src/org/sosy_lab/java_smt/utils/Parsers/smtlibv2.g4 by ANTLR 4.13.1
package org.sosy_lab.java_smt.utils.Parsers;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link smtlibv2Parser}.
 */
public interface smtlibv2Listener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart(smtlibv2Parser.StartContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart(smtlibv2Parser.StartContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void enterSimpleSymbol(smtlibv2Parser.SimpleSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void exitSimpleSymbol(smtlibv2Parser.SimpleSymbolContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void enterSymbol(smtlibv2Parser.SymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void exitSymbol(smtlibv2Parser.SymbolContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void enterKeyword(smtlibv2Parser.KeywordContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void exitKeyword(smtlibv2Parser.KeywordContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant(smtlibv2Parser.Spec_constantContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant(smtlibv2Parser.Spec_constantContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterS_expr(smtlibv2Parser.S_exprContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitS_expr(smtlibv2Parser.S_exprContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void enterIndex(smtlibv2Parser.IndexContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void exitIndex(smtlibv2Parser.IndexContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void enterIdentifier(smtlibv2Parser.IdentifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void exitIdentifier(smtlibv2Parser.IdentifierContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void enterAttribute_value(smtlibv2Parser.Attribute_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void exitAttribute_value(smtlibv2Parser.Attribute_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void enterAttribute(smtlibv2Parser.AttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void exitAttribute(smtlibv2Parser.AttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void enterSort(smtlibv2Parser.SortContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void exitSort(smtlibv2Parser.SortContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void enterQual_identifer(smtlibv2Parser.Qual_identiferContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#qual_identifer}.
	 * @param ctx the parse tree
	 */
	void exitQual_identifer(smtlibv2Parser.Qual_identiferContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void enterPattern(smtlibv2Parser.PatternContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void exitPattern(smtlibv2Parser.PatternContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(smtlibv2Parser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(smtlibv2Parser.TermContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterFun_symbol_decl(smtlibv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitFun_symbol_decl(smtlibv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterPar_fun_symbol_decl(smtlibv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitPar_fun_symbol_decl(smtlibv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_attribute(smtlibv2Parser.Theory_attributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_attribute(smtlibv2Parser.Theory_attributeContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_attribue(smtlibv2Parser.Logic_attribueContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_attribue(smtlibv2Parser.Logic_attribueContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void enterDatatype_dec(smtlibv2Parser.Datatype_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void exitDatatype_dec(smtlibv2Parser.Datatype_decContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void enterProp_literal(smtlibv2Parser.Prop_literalContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void exitProp_literal(smtlibv2Parser.Prop_literalContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterCommand(smtlibv2Parser.CommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitCommand(smtlibv2Parser.CommandContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterOption(smtlibv2Parser.OptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitOption(smtlibv2Parser.OptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterInfo_flag(smtlibv2Parser.Info_flagContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitInfo_flag(smtlibv2Parser.Info_flagContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void enterReason_unknown(smtlibv2Parser.Reason_unknownContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void exitReason_unknown(smtlibv2Parser.Reason_unknownContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void enterModel_response(smtlibv2Parser.Model_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void exitModel_response(smtlibv2Parser.Model_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_response(smtlibv2Parser.Info_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_response(smtlibv2Parser.Info_responseContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_model_response(smtlibv2Parser.Get_model_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_model_response(smtlibv2Parser.Get_model_responseContext ctx);
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
	 * Enter a parse tree produced by {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterSpecific_success_response(smtlibv2Parser.Specific_success_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitSpecific_success_response(smtlibv2Parser.Specific_success_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterGeneral_response(smtlibv2Parser.General_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link smtlibv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitGeneral_response(smtlibv2Parser.General_responseContext ctx);
}