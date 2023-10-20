package org.sosy_lab.java_smt.utils.Parsers;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.UFManager;


@SuppressWarnings("CheckReturnValue")
public class Visitor extends smtlibv2BaseVisitor<Object> {

  HashMap<String, ParserFormula> variables = new HashMap<String, ParserFormula>();
  Configuration config = Configuration.defaultConfiguration();
  LogManager logger = BasicLogManager.create(config);
  ShutdownManager shutdown = ShutdownManager.create();
  SolverContext context =
      SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
          Solvers.PRINCESS);
  FormulaManager fmgr = context.getFormulaManager();
  BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
  IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
  BitvectorFormulaManager bimgr = fmgr.getBitvectorFormulaManager();
  ArrayFormulaManager amgr = fmgr.getArrayFormulaManager();
  UFManager umgr = fmgr.getUFManager();

  public Visitor() throws InvalidConfigurationException {
  }

  @Override public Object visitStart(smtlibv2Parser.StartContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSimpleSymbol(smtlibv2Parser.SimpleSymbolContext ctx) {

    return ctx.children.get(0);
  }

  @Override public Object visitQuotedSymbol(smtlibv2Parser.QuotedSymbolContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPredefSymbol(smtlibv2Parser.PredefSymbolContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPredefKeyword(smtlibv2Parser.PredefKeywordContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSymbol(smtlibv2Parser.SymbolContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitNumeral(smtlibv2Parser.NumeralContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecimal(smtlibv2Parser.DecimalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitHexadecimal(smtlibv2Parser.HexadecimalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitBinary(smtlibv2Parser.BinaryContext ctx) { return visitChildren(ctx); }

  @Override public Object visitString(smtlibv2Parser.StringContext ctx) { return visitChildren(ctx); }

  @Override public Object visitKeyword(smtlibv2Parser.KeywordContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSpec_constant(smtlibv2Parser.Spec_constantContext ctx) { return visitChildren(ctx); }

  @Override public Object visitS_expr(smtlibv2Parser.S_exprContext ctx) { return visitChildren(ctx); }

  @Override public Object visitIndex(smtlibv2Parser.IndexContext ctx) { return visitChildren(ctx); }

  @Override public Object visitIdentifier(smtlibv2Parser.IdentifierContext ctx) {
    return visitChildren(ctx); }

  @Override public Object visitAttribute_value(smtlibv2Parser.Attribute_valueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAttribute(smtlibv2Parser.AttributeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSort(smtlibv2Parser.SortContext ctx) { return visitChildren(ctx); }

  @Override public Object visitQual_identifer(smtlibv2Parser.Qual_identiferContext ctx) { return visitChildren(ctx); }

  @Override public Object visitVar_binding(smtlibv2Parser.Var_bindingContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSorted_var(smtlibv2Parser.Sorted_varContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPattern(smtlibv2Parser.PatternContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMatch_case(smtlibv2Parser.Match_caseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTerm(smtlibv2Parser.TermContext ctx) {
    String bla = ctx.getText();
    System.out.println(ctx + " " + ctx.getText());
    System.out.println();
    String operator = ctx.qual_identifer().getText();
    // if and
    // PLAN: bmgr.and(recursive -> bmgr);

    List<String> operands = new ArrayList<>();
    for (int i = 0; i < ctx.term().size(); i++) {
      operands.add(ctx.term(i).getText());
      }
    //System.out.println(operator);
    //System.out.println(operands);
    //return bmgr.and(visitChildren((RuleNode)visitTerm(ctx)),visitChildren((RuleNode)visitTerm(ctx)));
    return visitChildren(ctx);
  }

  @Override public Object visitSort_symbol_decl(smtlibv2Parser.Sort_symbol_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMeta_spec_constant(smtlibv2Parser.Meta_spec_constantContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFun_symbol_decl(smtlibv2Parser.Fun_symbol_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPar_fun_symbol_decl(smtlibv2Parser.Par_fun_symbol_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_attribute(smtlibv2Parser.Theory_attributeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_decl(smtlibv2Parser.Theory_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_attribue(smtlibv2Parser.Logic_attribueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic(smtlibv2Parser.LogicContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSort_dec(smtlibv2Parser.Sort_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSelector_dec(smtlibv2Parser.Selector_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitConstructor_dec(smtlibv2Parser.Constructor_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDatatype_dec(smtlibv2Parser.Datatype_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFunction_dec(smtlibv2Parser.Function_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFunction_def(smtlibv2Parser.Function_defContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProp_literal(smtlibv2Parser.Prop_literalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitScript(smtlibv2Parser.ScriptContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_assert(smtlibv2Parser.Cmd_assertContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitCmd_checkSat(smtlibv2Parser.Cmd_checkSatContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_checkSatAssuming(smtlibv2Parser.Cmd_checkSatAssumingContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_declareConst(smtlibv2Parser.Cmd_declareConstContext ctx) {
    String variable = ctx.symbol().getText();
    String sort = ctx.sort().getText();
    if (sort.equals("Bool")) {
      variables.put(variable, new ParserFormula("Bool", bmgr.makeVariable(variable)));
    } else if (sort.equals("Int")) {
      variables.put((variable), new ParserFormula("Int", bmgr.and(bmgr.makeVariable("p"))));
    } else {
      variables.put((variable), new ParserFormula("UF", bmgr.makeVariable(variable)));
    }
    return visitChildren(ctx);
  }

  @Override public Object visitCmd_declareDatatype(smtlibv2Parser.Cmd_declareDatatypeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_declareDatatypes(smtlibv2Parser.Cmd_declareDatatypesContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_declareFun(smtlibv2Parser.Cmd_declareFunContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_defineFun(smtlibv2Parser.Cmd_defineFunContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_defineFunRec(smtlibv2Parser.Cmd_defineFunRecContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_defineFunsRec(smtlibv2Parser.Cmd_defineFunsRecContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_defineSort(smtlibv2Parser.Cmd_defineSortContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_echo(smtlibv2Parser.Cmd_echoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_exit(smtlibv2Parser.Cmd_exitContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getAssertions(smtlibv2Parser.Cmd_getAssertionsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getAssignment(smtlibv2Parser.Cmd_getAssignmentContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getInfo(smtlibv2Parser.Cmd_getInfoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getModel(smtlibv2Parser.Cmd_getModelContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getOption(smtlibv2Parser.Cmd_getOptionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getProof(smtlibv2Parser.Cmd_getProofContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getUnsatAssumptions(smtlibv2Parser.Cmd_getUnsatAssumptionsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getUnsatCore(smtlibv2Parser.Cmd_getUnsatCoreContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_getValue(smtlibv2Parser.Cmd_getValueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_pop(smtlibv2Parser.Cmd_popContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_push(smtlibv2Parser.Cmd_pushContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_reset(smtlibv2Parser.Cmd_resetContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_resetAssertions(smtlibv2Parser.Cmd_resetAssertionsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_setInfo(smtlibv2Parser.Cmd_setInfoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_setLogic(smtlibv2Parser.Cmd_setLogicContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_setOption(smtlibv2Parser.Cmd_setOptionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCommand(smtlibv2Parser.CommandContext ctx) {
    return visitChildren(ctx);
  }

  @Override public Object visitB_value(smtlibv2Parser.B_valueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitOption(smtlibv2Parser.OptionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_flag(smtlibv2Parser.Info_flagContext ctx) { return visitChildren(ctx); }

  @Override public Object visitError_behaviour(smtlibv2Parser.Error_behaviourContext ctx) { return visitChildren(ctx); }

  @Override public Object visitReason_unknown(smtlibv2Parser.Reason_unknownContext ctx) { return visitChildren(ctx); }

  @Override public Object visitModel_response(smtlibv2Parser.Model_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_response(smtlibv2Parser.Info_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitValuation_pair(smtlibv2Parser.Valuation_pairContext ctx) { return visitChildren(ctx); }

  @Override public Object visitT_valuation_pair(smtlibv2Parser.T_valuation_pairContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCheck_sat_response(smtlibv2Parser.Check_sat_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitEcho_response(smtlibv2Parser.Echo_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assertions_response(smtlibv2Parser.Get_assertions_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assignment_response(smtlibv2Parser.Get_assignment_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_info_response(smtlibv2Parser.Get_info_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_model_response(smtlibv2Parser.Get_model_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_option_response(smtlibv2Parser.Get_option_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_proof_response(smtlibv2Parser.Get_proof_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_assump_response(smtlibv2Parser.Get_unsat_assump_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_core_response(smtlibv2Parser.Get_unsat_core_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_value_response(smtlibv2Parser.Get_value_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSpecific_success_response(smtlibv2Parser.Specific_success_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGeneral_response(smtlibv2Parser.General_responseContext ctx) { return visitChildren(ctx); }
}