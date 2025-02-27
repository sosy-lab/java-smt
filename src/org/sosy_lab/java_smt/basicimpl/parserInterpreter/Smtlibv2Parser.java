// Generated from
// /home/dalux/Dokumente/IdeaProjects/java-smt/src/org/
// sosy_lab/javaSmt/basicimpl/parserInterpreter/smtlibv2.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import java.util.List;
import org.antlr.v4.runtime.NoViableAltException;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.RuntimeMetaData;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.Vocabulary;
import org.antlr.v4.runtime.VocabularyImpl;
import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNDeserializer;
import org.antlr.v4.runtime.atn.ParserATNSimulator;
import org.antlr.v4.runtime.atn.PredictionContextCache;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.antlr.v4.runtime.tree.TerminalNode;

@SuppressWarnings({
  "all",
  "UnnecessaryParentheses",
  "warnings",
  "unchecked",
  "unused",
  "cast",
  "CheckReturnValue",
  "this-escape"
})
public class Smtlibv2Parser extends Parser {
  static {
    RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION);
  }

  protected static final DFA[] decisionToDFA;
  protected static final PredictionContextCache sharedContextCache = new PredictionContextCache();
  public static final int Comment = 1,
      ParOpen = 2,
      ParClose = 3,
      Semicolon = 4,
      String = 5,
      QuotedSymbol = 6,
      PSNot = 7,
      PSBool = 8,
      PSContinuedExecution = 9,
      PSError = 10,
      PSFalse = 11,
      PSImmediateExit = 12,
      PSIncomplete = 13,
      PSLogic = 14,
      PSMemout = 15,
      PSSat = 16,
      PSSuccess = 17,
      PSTheory = 18,
      PSTrue = 19,
      PSUnknown = 20,
      PSUnsupported = 21,
      PSUnsat = 22,
      CMDAssert = 23,
      CMDCheckSat = 24,
      CMDCheckSatAssuming = 25,
      CMDDeclareConst = 26,
      CMDDeclareDatatype = 27,
      CMDDeclareDatatypes = 28,
      CMDDeclareFun = 29,
      CMDDeclareSort = 30,
      CMDDefineFun = 31,
      CMDDefineFunRec = 32,
      CMDDefineFunsRec = 33,
      CMDDefineSort = 34,
      CMDEcho = 35,
      CMDExit = 36,
      CMDGetAssertions = 37,
      CMDGetAssignment = 38,
      CMDGetInfo = 39,
      CMDGetModel = 40,
      CMDGetOption = 41,
      CMDGetProof = 42,
      CMDGetUnsatAssumptions = 43,
      CMDGetUnsatCore = 44,
      CMDGetValue = 45,
      CMDPop = 46,
      CMDPush = 47,
      CMDReset = 48,
      CMDResetAssertions = 49,
      CMDSetInfo = 50,
      CMDSetLogic = 51,
      CMDSetOption = 52,
      GRWExclamation = 53,
      GRWUnderscore = 54,
      GRWAs = 55,
      GRWBinary = 56,
      GRWDecimal = 57,
      GRWExists = 58,
      GRWHexadecimal = 59,
      GRWForall = 60,
      GRWLet = 61,
      GRWMatch = 62,
      GRWNumeral = 63,
      GRWPar = 64,
      GRWString = 65,
      Numeral = 66,
      Binary = 67,
      HexDecimal = 68,
      Decimal = 69,
      NumeralExponentsWithSpace = 70,
      FloatingPointNumeral = 71,
      FloatingPointShortVariant = 72,
      NumeralFloatingPoint = 73,
      BinaryFloatingPoint = 74,
      HexadecimalFloatingPoint = 75,
      FloatingPointPlusOrMinusInfinity = 76,
      FloatingPointPlusOrMinusZero = 77,
      NotANumberFloatingPoint = 78,
      FloatingPoint = 79,
      Colon = 80,
      PKAllStatistics = 81,
      PKAssertionStackLevels = 82,
      PKAuthors = 83,
      PKCategory = 84,
      PKChainable = 85,
      PKDefinition = 86,
      PKDiagnosticOutputChannel = 87,
      PKErrorBehaviour = 88,
      PKExtension = 89,
      PKFuns = 90,
      PKFunsDescription = 91,
      PKGlobalDeclarations = 92,
      PKInteractiveMode = 93,
      PKLanguage = 94,
      PKLeftAssoc = 95,
      PKLicense = 96,
      PKNamed = 97,
      PKName = 98,
      PKNotes = 99,
      PKPattern = 100,
      PKPrintSuccess = 101,
      PKProduceAssertions = 102,
      PKProduceAssignments = 103,
      PKProduceModels = 104,
      PKProduceProofs = 105,
      PKProduceUnsatAssumptions = 106,
      PKProduceUnsatCores = 107,
      PKRandomSeed = 108,
      PKReasonUnknown = 109,
      PKRegularOutputChannel = 110,
      PKReproducibleResourceLimit = 111,
      PKRightAssoc = 112,
      PKSmtLibVersion = 113,
      PKSorts = 114,
      PKSortsDescription = 115,
      PKSource = 116,
      PKStatus = 117,
      PKTheories = 118,
      PKValues = 119,
      PKVerbosity = 120,
      PKVersion = 121,
      RSModel = 122,
      UndefinedSymbol = 123,
      WS = 124;
  public static final int RULEstart = 0,
      RULEgeneralReservedWord = 1,
      RULEsimpleSymbol = 2,
      RULEquotedSymbol = 3,
      RULEpredefSymbol = 4,
      RULEpredefKeyword = 5,
      RULEsymbol = 6,
      RULEnumeral = 7,
      RULEdecimal = 8,
      RULEhexadecimal = 9,
      RULEbinary = 10,
      RULEstring = 11,
      RULEfloatingpoint = 12,
      RULEkeyword = 13,
      RULEspecconstant = 14,
      RULEsexpr = 15,
      RULEindex = 16,
      RULEidentifier = 17,
      RULEattributevalue = 18,
      RULEattribute = 19,
      RULEsort = 20,
      RULEqualidentifer = 21,
      RULEvarbinding = 22,
      RULEsortedvar = 23,
      RULEpattern = 24,
      RULEmatchcase = 25,
      RULEterm = 26,
      RULEsortsymboldecl = 27,
      RULEmetaspecconstant = 28,
      RULEfunsymboldecl = 29,
      RULEparfunsymboldecl = 30,
      RULEtheoryattribute = 31,
      RULEtheorydecl = 32,
      RULElogicattribue = 33,
      RULElogic = 34,
      RULEsortdec = 35,
      RULEselectordec = 36,
      RULEconstructordec = 37,
      RULEdatatypedec = 38,
      RULEfunctiondec = 39,
      RULEfunctiondef = 40,
      RULEpropliteral = 41,
      RULEscript = 42,
      RULEcmdassert = 43,
      RULEcmdcheckSat = 44,
      RULEcmdcheckSatAssuming = 45,
      RULEcmddeclareConst = 46,
      RULEcmddeclareDatatype = 47,
      RULEcmddeclareDatatypes = 48,
      RULEcmddeclareFun = 49,
      RULEcmddeclareSort = 50,
      RULEcmddefineFun = 51,
      RULEcmddefineFunRec = 52,
      RULEcmddefineFunsRec = 53,
      RULEcmddefineSort = 54,
      RULEcmdecho = 55,
      RULEcmdexit = 56,
      RULEcmdgetAssertions = 57,
      RULEcmdgetAssignment = 58,
      RULEcmdgetInfo = 59,
      RULEcmdgetModel = 60,
      RULEcmdgetOption = 61,
      RULEcmdgetProof = 62,
      RULEcmdgetUnsatAssumptions = 63,
      RULEcmdgetUnsatCore = 64,
      RULEcmdgetValue = 65,
      RULEcmdpop = 66,
      RULEcmdpush = 67,
      RULEcmdreset = 68,
      RULEcmdresetAssertions = 69,
      RULEcmdsetInfo = 70,
      RULEcmdsetLogic = 71,
      RULEcmdsetOption = 72,
      RULEcommand = 73,
      RULEbvalue = 74,
      RULEoption = 75,
      RULEinfoflag = 76,
      RULEerrorbehaviour = 77,
      RULEreasonunknown = 78,
      RULEmodelresponse = 79,
      RULEinforesponse = 80,
      RULEvaluationpair = 81,
      RULEtvaluationpair = 82,
      RULEchecksatresponse = 83,
      RULEechoresponse = 84,
      RULEgetassertionsresponse = 85,
      RULEgetassignmentresponse = 86,
      RULEgetinforesponse = 87,
      RULEgetmodelresponse = 88,
      RULEgetoptionresponse = 89,
      RULEgetproofresponse = 90,
      RULEgetunsatassumpresponse = 91,
      RULEgetunsatcoreresponse = 92,
      RULEgetvalueresponse = 93,
      RULEspecificsuccessresponse = 94,
      RULEgeneralresponse = 95;

  private static String[] makeRuleNames() {
    return new String[] {
      "start",
      "generalReservedWord",
      "simpleSymbol",
      "quotedSymbol",
      "predefSymbol",
      "predefKeyword",
      "symbol",
      "numeral",
      "decimal",
      "hexadecimal",
      "binary",
      "string",
      "floatingpoint",
      "keyword",
      "specconstant",
      "sexpr",
      "index",
      "identifier",
      "attributevalue",
      "attribute",
      "sort",
      "qualidentifer",
      "varbinding",
      "sortedvar",
      "pattern",
      "matchcase",
      "term",
      "sortsymboldecl",
      "metaspecconstant",
      "funsymboldecl",
      "parfunsymboldecl",
      "theoryattribute",
      "theorydecl",
      "logicattribue",
      "logic",
      "sortdec",
      "selectordec",
      "constructordec",
      "datatypedec",
      "functiondec",
      "functiondef",
      "propliteral",
      "script",
      "cmdassert",
      "cmdcheckSat",
      "cmdcheckSatAssuming",
      "cmddeclareConst",
      "cmddeclareDatatype",
      "cmddeclareDatatypes",
      "cmddeclareFun",
      "cmddeclareSort",
      "cmddefineFun",
      "cmddefineFunRec",
      "cmddefineFunsRec",
      "cmddefineSort",
      "cmdecho",
      "cmdexit",
      "cmdgetAssertions",
      "cmdgetAssignment",
      "cmdgetInfo",
      "cmdgetModel",
      "cmdgetOption",
      "cmdgetProof",
      "cmdgetUnsatAssumptions",
      "cmdgetUnsatCore",
      "cmdgetValue",
      "cmdpop",
      "cmdpush",
      "cmdreset",
      "cmdresetAssertions",
      "cmdsetInfo",
      "cmdsetLogic",
      "cmdsetOption",
      "command",
      "bvalue",
      "option",
      "infoflag",
      "errorbehaviour",
      "reasonunknown",
      "modelresponse",
      "inforesponse",
      "valuationpair",
      "tvaluationpair",
      "checksatresponse",
      "echoresponse",
      "getassertionsresponse",
      "getassignmentresponse",
      "getinforesponse",
      "getmodelresponse",
      "getoptionresponse",
      "getproofresponse",
      "getunsatassumpresponse",
      "getunsatcoreresponse",
      "getvalueresponse",
      "specificsuccessresponse",
      "generalresponse"
    };
  }

  public static final String[] ruleNames = makeRuleNames();

  private static String[] makeLiteralNames() {
    return new String[] {
      null,
      null,
      "'('",
      "')'",
      "';'",
      null,
      null,
      "'not'",
      "'Bool'",
      "'continued-execution'",
      "'error'",
      "'false'",
      "'immediate-exit'",
      "'incomplete'",
      "'logic'",
      "'memout'",
      "'sat'",
      "'success'",
      "'theory'",
      "'true'",
      "'unknown'",
      "'unsupported'",
      "'unsat'",
      "'assert'",
      "'check-sat'",
      "'check-sat-assuming'",
      "'declare-const'",
      "'declare-datatype'",
      "'declare-datatypes'",
      "'declare-fun'",
      "'declare-sort'",
      "'define-fun'",
      "'define-fun-rec'",
      "'define-funs-rec'",
      "'define-sort'",
      "'echo'",
      "'exit'",
      "'get-assertions'",
      "'get-assignment'",
      "'get-info'",
      "'get-model'",
      "'get-option'",
      "'get-proof'",
      "'get-unsat-assumptions'",
      "'get-unsat-core'",
      "'get-value'",
      "'pop'",
      "'push'",
      "'reset'",
      "'reset-assertions'",
      "'set-info'",
      "'set-logic'",
      "'set-option'",
      "'!'",
      "''",
      "'as'",
      "'BINARY'",
      "'DECIMAL'",
      "'exists'",
      "'HEXADECIMAL'",
      "'forall'",
      "'let'",
      "'match'",
      "'NUMERAL'",
      "'par'",
      "'string'",
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      null,
      "':'",
      "':all-statistics'",
      "':assertion-stack-levels'",
      "':authors'",
      "':category'",
      "':chainable'",
      "':definition'",
      "':diagnostic-output-channel'",
      "':error-behavior'",
      "':extensions'",
      "':funs'",
      "':funs-description'",
      "':global-declarations'",
      "':interactive-mode'",
      "':language'",
      "':left-assoc'",
      "':license'",
      "':named'",
      "':name'",
      "':notes'",
      "':pattern'",
      "':print-success'",
      "':produce-assertions'",
      "':produce-assignments'",
      "':produce-models'",
      "':produce-proofs'",
      "':produce-unsat-assumptions'",
      "':produce-unsat-cores'",
      "':random-seed'",
      "':reason-unknown'",
      "':regular-output-channel'",
      "':reproducible-resource-limit'",
      "':right-assoc'",
      "':smt-lib-version'",
      "':sorts'",
      "':sorts-description'",
      "':source'",
      "':status'",
      "':theories'",
      "':values'",
      "':verbosity'",
      "':version'",
      "'model'"
    };
  }

  private static final String[] LITERALNAMES = makeLiteralNames();

  private static String[] makeSymbolicNames() {
    return new String[] {
      null,
      "Comment",
      "ParOpen",
      "ParClose",
      "Semicolon",
      "String",
      "QuotedSymbol",
      "PSNot",
      "PSBool",
      "PSContinuedExecution",
      "PSError",
      "PSFalse",
      "PSImmediateExit",
      "PSIncomplete",
      "PSLogic",
      "PSMemout",
      "PSSat",
      "PSSuccess",
      "PSTheory",
      "PSTrue",
      "PSUnknown",
      "PSUnsupported",
      "PSUnsat",
      "CMDAssert",
      "CMDCheckSat",
      "CMDCheckSatAssuming",
      "CMDDeclareConst",
      "CMDDeclareDatatype",
      "CMDDeclareDatatypes",
      "CMDDeclareFun",
      "CMDDeclareSort",
      "CMDDefineFun",
      "CMDDefineFunRec",
      "CMDDefineFunsRec",
      "CMDDefineSort",
      "CMDEcho",
      "CMDExit",
      "CMDGetAssertions",
      "CMDGetAssignment",
      "CMDGetInfo",
      "CMDGetModel",
      "CMDGetOption",
      "CMDGetProof",
      "CMDGetUnsatAssumptions",
      "CMDGetUnsatCore",
      "CMDGetValue",
      "CMDPop",
      "CMDPush",
      "CMDReset",
      "CMDResetAssertions",
      "CMDSetInfo",
      "CMDSetLogic",
      "CMDSetOption",
      "GRWExclamation",
      "GRWUnderscore",
      "GRWAs",
      "GRWBinary",
      "GRWDecimal",
      "GRWExists",
      "GRWHexadecimal",
      "GRWForall",
      "GRWLet",
      "GRWMatch",
      "GRWNumeral",
      "GRWPar",
      "GRWString",
      "Numeral",
      "Binary",
      "HexDecimal",
      "Decimal",
      "NumeralExponentsWithSpace",
      "FloatingPointNumeral",
      "FloatingPointShortVariant",
      "NumeralFloatingPoint",
      "BinaryFloatingPoint",
      "HexadecimalFloatingPoint",
      "FloatingPointPlusOrMinusInfinity",
      "FloatingPointPlusOrMinusZero",
      "NotANumberFloatingPoint",
      "FloatingPoint",
      "Colon",
      "PKAllStatistics",
      "PKAssertionStackLevels",
      "PKAuthors",
      "PKCategory",
      "PKChainable",
      "PKDefinition",
      "PKDiagnosticOutputChannel",
      "PKErrorBehaviour",
      "PKExtension",
      "PKFuns",
      "PKFunsDescription",
      "PKGlobalDeclarations",
      "PKInteractiveMode",
      "PKLanguage",
      "PKLeftAssoc",
      "PKLicense",
      "PKNamed",
      "PKName",
      "PKNotes",
      "PKPattern",
      "PKPrintSuccess",
      "PKProduceAssertions",
      "PKProduceAssignments",
      "PKProduceModels",
      "PKProduceProofs",
      "PKProduceUnsatAssumptions",
      "PKProduceUnsatCores",
      "PKRandomSeed",
      "PKReasonUnknown",
      "PKRegularOutputChannel",
      "PKReproducibleResourceLimit",
      "PKRightAssoc",
      "PKSmtLibVersion",
      "PKSorts",
      "PKSortsDescription",
      "PKSource",
      "PKStatus",
      "PKTheories",
      "PKValues",
      "PKVerbosity",
      "PKVersion",
      "RSModel",
      "UndefinedSymbol",
      "WS"
    };
  }

  private static final String[] SYMBOLICNAMES = makeSymbolicNames();
  public static final Vocabulary VOCABULARY = new VocabularyImpl(LITERALNAMES, SYMBOLICNAMES);

  /**
   * @deprecated Use {@link #VOCABULARY} instead.
   */
  @Deprecated public static final String[] tokenNames;

  static {
    tokenNames = new String[SYMBOLICNAMES.length];
    for (int i = 0; i < tokenNames.length; i++) {
      tokenNames[i] = VOCABULARY.getLiteralName(i);
      if (tokenNames[i] == null) {
        tokenNames[i] = VOCABULARY.getSymbolicName(i);
      }

      if (tokenNames[i] == null) {
        tokenNames[i] = "<INVALID>";
      }
    }
  }

  @Override
  @Deprecated
  public String[] getTokenNames() {
    return tokenNames;
  }

  @Override
  public Vocabulary getVocabulary() {
    return VOCABULARY;
  }

  @Override
  public String getGrammarFileName() {
    return "smtlibv2.g4";
  }

  @Override
  public String[] getRuleNames() {
    return ruleNames;
  }

  @Override
  public String getSerializedATN() {
    return serializedATN;
  }

  @Override
  public ATN getATN() {
    return ATN;
  }

  public Smtlibv2Parser(TokenStream _input) {
    super(_input);
    _interp = new ParserATNSimulator(this, ATN, decisionToDFA, sharedContextCache);
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StartContext extends ParserRuleContext {
    public StartContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEstart;
    }

    public StartContext() {}

    public void copyFrom(StartContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StartscriptContext extends StartContext {
    public ScriptContext script() {
      return getRuleContext(ScriptContext.class, 0);
    }

    public TerminalNode EOF() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.EOF, 0);
    }

    public StartscriptContext(StartContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterStartscript(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitStartscript(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitStartscript(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StartgenrespContext extends StartContext {
    public GeneralresponseContext generalresponse() {
      return getRuleContext(GeneralresponseContext.class, 0);
    }

    public TerminalNode EOF() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.EOF, 0);
    }

    public StartgenrespContext(StartContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterStartgenresp(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitStartgenresp(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitStartgenresp(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StartlogicContext extends StartContext {
    public LogicContext logic() {
      return getRuleContext(LogicContext.class, 0);
    }

    public TerminalNode EOF() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.EOF, 0);
    }

    public StartlogicContext(StartContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterStartlogic(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitStartlogic(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitStartlogic(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StarttheoryContext extends StartContext {
    public TheorydeclContext theorydecl() {
      return getRuleContext(TheorydeclContext.class, 0);
    }

    public TerminalNode EOF() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.EOF, 0);
    }

    public StarttheoryContext(StartContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterStarttheory(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitStarttheory(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitStarttheory(this);
      else return visitor.visitChildren(this);
    }
  }

  public final StartContext start() throws RecognitionException {
    StartContext local_ctx = new StartContext(_ctx, getState());
    enterRule(local_ctx, 0, RULEstart);
    try {
      setState(204);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 0, _ctx)) {
        case 1:
          local_ctx = new StartlogicContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(192);
            logic();
            setState(193);
            match(EOF);
          }
          break;
        case 2:
          local_ctx = new StarttheoryContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(195);
            theorydecl();
            setState(196);
            match(EOF);
          }
          break;
        case 3:
          local_ctx = new StartscriptContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(198);
            script();
            setState(199);
            match(EOF);
          }
          break;
        case 4:
          local_ctx = new StartgenrespContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(201);
            generalresponse();
            setState(202);
            match(EOF);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GeneralReservedWordContext extends ParserRuleContext {
    public TerminalNode GRWExclamation() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWExclamation, 0);
    }

    public TerminalNode GRWUnderscore() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWUnderscore, 0);
    }

    public TerminalNode GRWAs() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWAs, 0);
    }

    public TerminalNode GRWBinary() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWBinary, 0);
    }

    public TerminalNode GRWDecimal() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWDecimal, 0);
    }

    public TerminalNode GRWExists() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWExists, 0);
    }

    public TerminalNode GRWHexadecimal() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWHexadecimal, 0);
    }

    public TerminalNode GRWForall() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWForall, 0);
    }

    public TerminalNode GRWLet() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWLet, 0);
    }

    public TerminalNode GRWMatch() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWMatch, 0);
    }

    public TerminalNode GRWNumeral() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWNumeral, 0);
    }

    public TerminalNode GRWPar() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWPar, 0);
    }

    public TerminalNode GRWString() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWString, 0);
    }

    public TerminalNode RSModel() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.RSModel, 0);
    }

    public GeneralReservedWordContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgeneralReservedWord;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGeneralReservedWord(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGeneralReservedWord(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGeneralReservedWord(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GeneralReservedWordContext generalReservedWord() throws RecognitionException {
    GeneralReservedWordContext local_ctx = new GeneralReservedWordContext(_ctx, getState());
    enterRule(local_ctx, 2, RULEgeneralReservedWord);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(206);
        la = _input.LA(1);
        if (!((((la) & ~0x3f) == 0 && ((1L << la) & -9007199254740992L) != 0)
            || ((((la - 64)) & ~0x3f) == 0 && ((1L << (la - 64)) & 288230376151711747L) != 0))) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SimpleSymbolContext extends ParserRuleContext {
    public SimpleSymbolContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsimpleSymbol;
    }

    public SimpleSymbolContext() {}

    public void copyFrom(SimpleSymbolContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SimppresymbContext extends SimpleSymbolContext {
    public PredefSymbolContext predefSymbol() {
      return getRuleContext(PredefSymbolContext.class, 0);
    }

    public SimppresymbContext(SimpleSymbolContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSimppresymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSimppresymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSimppresymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SimpundefsymbContext extends SimpleSymbolContext {
    public TerminalNode UndefinedSymbol() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.UndefinedSymbol, 0);
    }

    public SimpundefsymbContext(SimpleSymbolContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSimpundefsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSimpundefsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSimpundefsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SimpleSymbolContext simpleSymbol() throws RecognitionException {
    SimpleSymbolContext local_ctx = new SimpleSymbolContext(_ctx, getState());
    enterRule(local_ctx, 4, RULEsimpleSymbol);
    try {
      setState(210);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
          local_ctx = new SimppresymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(208);
            predefSymbol();
          }
          break;
        case UndefinedSymbol:
          local_ctx = new SimpundefsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(209);
            match(UndefinedSymbol);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QuotedSymbolContext extends ParserRuleContext {
    public TerminalNode QuotedSymbol() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.QuotedSymbol, 0);
    }

    public QuotedSymbolContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEquotedSymbol;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterQuotedSymbol(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitQuotedSymbol(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitQuotedSymbol(this);
      else return visitor.visitChildren(this);
    }
  }

  public final QuotedSymbolContext quotedSymbol() throws RecognitionException {
    QuotedSymbolContext local_ctx = new QuotedSymbolContext(_ctx, getState());
    enterRule(local_ctx, 6, RULEquotedSymbol);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(212);
        match(QuotedSymbol);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PredefSymbolContext extends ParserRuleContext {
    public TerminalNode PSNot() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSNot, 0);
    }

    public TerminalNode PSBool() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSBool, 0);
    }

    public TerminalNode PSContinuedExecution() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSContinuedExecution, 0);
    }

    public TerminalNode PSError() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSError, 0);
    }

    public TerminalNode PSFalse() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSFalse, 0);
    }

    public TerminalNode PSImmediateExit() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSImmediateExit, 0);
    }

    public TerminalNode PSIncomplete() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSIncomplete, 0);
    }

    public TerminalNode PSLogic() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSLogic, 0);
    }

    public TerminalNode PSMemout() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSMemout, 0);
    }

    public TerminalNode PSSat() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSSat, 0);
    }

    public TerminalNode PSSuccess() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSSuccess, 0);
    }

    public TerminalNode PSTheory() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSTheory, 0);
    }

    public TerminalNode PSTrue() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSTrue, 0);
    }

    public TerminalNode PSUnknown() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnknown, 0);
    }

    public TerminalNode PSUnsupported() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnsupported, 0);
    }

    public TerminalNode PSUnsat() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnsat, 0);
    }

    public PredefSymbolContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEpredefSymbol;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterPredefSymbol(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitPredefSymbol(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPredefSymbol(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PredefSymbolContext predefSymbol() throws RecognitionException {
    PredefSymbolContext local_ctx = new PredefSymbolContext(_ctx, getState());
    enterRule(local_ctx, 8, RULEpredefSymbol);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(214);
        la = _input.LA(1);
        if (!((((la) & ~0x3f) == 0 && ((1L << la) & 8388480L) != 0))) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PredefKeywordContext extends ParserRuleContext {
    public TerminalNode PKAllStatistics() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAllStatistics, 0);
    }

    public TerminalNode PKAssertionStackLevels() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAssertionStackLevels,
          0);
    }

    public TerminalNode PKAuthors() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAuthors, 0);
    }

    public TerminalNode PKCategory() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKCategory, 0);
    }

    public TerminalNode PKChainable() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKChainable, 0);
    }

    public TerminalNode PKDefinition() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKDefinition, 0);
    }

    public TerminalNode PKDiagnosticOutputChannel() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKDiagnosticOutputChannel,
          0);
    }

    public TerminalNode PKErrorBehaviour() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKErrorBehaviour, 0);
    }

    public TerminalNode PKExtension() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKExtension, 0);
    }

    public TerminalNode PKFuns() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKFuns, 0);
    }

    public TerminalNode PKFunsDescription() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKFunsDescription, 0);
    }

    public TerminalNode PKGlobalDeclarations() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKGlobalDeclarations, 0);
    }

    public TerminalNode PKInteractiveMode() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKInteractiveMode, 0);
    }

    public TerminalNode PKLanguage() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKLanguage, 0);
    }

    public TerminalNode PKLeftAssoc() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKLeftAssoc, 0);
    }

    public TerminalNode PKLicense() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKLicense, 0);
    }

    public TerminalNode PKNamed() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKNamed, 0);
    }

    public TerminalNode PKName() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKName, 0);
    }

    public TerminalNode PKNotes() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKNotes, 0);
    }

    public TerminalNode PKPattern() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKPattern, 0);
    }

    public TerminalNode PKPrintSuccess() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKPrintSuccess, 0);
    }

    public TerminalNode PKProduceAssertions() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceAssertions, 0);
    }

    public TerminalNode PKProduceAssignments() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceAssignments, 0);
    }

    public TerminalNode PKProduceModels() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceModels, 0);
    }

    public TerminalNode PKProduceProofs() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceProofs, 0);
    }

    public TerminalNode PKProduceUnsatAssumptions() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKProduceUnsatAssumptions,
          0);
    }

    public TerminalNode PKProduceUnsatCores() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceUnsatCores, 0);
    }

    public TerminalNode PKRandomSeed() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKRandomSeed, 0);
    }

    public TerminalNode PKReasonUnknown() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKReasonUnknown, 0);
    }

    public TerminalNode PKRegularOutputChannel() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKRegularOutputChannel,
          0);
    }

    public TerminalNode PKReproducibleResourceLimit() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKReproducibleResourceLimit,
          0);
    }

    public TerminalNode PKRightAssoc() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKRightAssoc, 0);
    }

    public TerminalNode PKSmtLibVersion() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSmtLibVersion, 0);
    }

    public TerminalNode PKSorts() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSorts, 0);
    }

    public TerminalNode PKSortsDescription() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSortsDescription, 0);
    }

    public TerminalNode PKSource() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSource, 0);
    }

    public TerminalNode PKStatus() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKStatus, 0);
    }

    public TerminalNode PKTheories() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKTheories, 0);
    }

    public TerminalNode PKValues() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKValues, 0);
    }

    public TerminalNode PKVerbosity() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKVerbosity, 0);
    }

    public TerminalNode PKVersion() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKVersion, 0);
    }

    public PredefKeywordContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEpredefKeyword;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterPredefKeyword(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitPredefKeyword(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPredefKeyword(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PredefKeywordContext predefKeyword() throws RecognitionException {
    PredefKeywordContext local_ctx = new PredefKeywordContext(_ctx, getState());
    enterRule(local_ctx, 10, RULEpredefKeyword);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(216);
        la = _input.LA(1);
        if (!(((((la - 81)) & ~0x3f) == 0 && ((1L << (la - 81)) & 2199023255551L) != 0))) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SymbolContext extends ParserRuleContext {
    public SymbolContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsymbol;
    }

    public SymbolContext() {}

    public void copyFrom(SymbolContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SimpsymbContext extends SymbolContext {
    public SimpleSymbolContext simpleSymbol() {
      return getRuleContext(SimpleSymbolContext.class, 0);
    }

    public SimpsymbContext(SymbolContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSimpsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSimpsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSimpsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QuotsymbContext extends SymbolContext {
    public QuotedSymbolContext quotedSymbol() {
      return getRuleContext(QuotedSymbolContext.class, 0);
    }

    public QuotsymbContext(SymbolContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterQuotsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitQuotsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitQuotsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SymbolContext symbol() throws RecognitionException {
    SymbolContext local_ctx = new SymbolContext(_ctx, getState());
    enterRule(local_ctx, 12, RULEsymbol);
    try {
      setState(220);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new SimpsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(218);
            simpleSymbol();
          }
          break;
        case QuotedSymbol:
          local_ctx = new QuotsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(219);
            quotedSymbol();
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class NumeralContext extends ParserRuleContext {
    public TerminalNode Numeral() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.Numeral, 0);
    }

    public NumeralContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEnumeral;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterNumeral(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitNumeral(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitNumeral(this);
      else return visitor.visitChildren(this);
    }
  }

  public final NumeralContext numeral() throws RecognitionException {
    NumeralContext local_ctx = new NumeralContext(_ctx, getState());
    enterRule(local_ctx, 14, RULEnumeral);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(222);
        match(Numeral);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DecimalContext extends ParserRuleContext {
    public TerminalNode Decimal() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.Decimal, 0);
    }

    public DecimalContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEdecimal;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDecimal(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDecimal(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDecimal(this);
      else return visitor.visitChildren(this);
    }
  }

  public final DecimalContext decimal() throws RecognitionException {
    DecimalContext local_ctx = new DecimalContext(_ctx, getState());
    enterRule(local_ctx, 16, RULEdecimal);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(224);
        match(Decimal);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class HexadecimalContext extends ParserRuleContext {
    public TerminalNode HexDecimal() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.HexDecimal, 0);
    }

    public HexadecimalContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEhexadecimal;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterHexadecimal(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitHexadecimal(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitHexadecimal(this);
      else return visitor.visitChildren(this);
    }
  }

  public final HexadecimalContext hexadecimal() throws RecognitionException {
    HexadecimalContext local_ctx = new HexadecimalContext(_ctx, getState());
    enterRule(local_ctx, 18, RULEhexadecimal);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(226);
        match(HexDecimal);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class BinaryContext extends ParserRuleContext {
    public TerminalNode Binary() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.Binary, 0);
    }

    public BinaryContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEbinary;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterBinary(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitBinary(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitBinary(this);
      else return visitor.visitChildren(this);
    }
  }

  public final BinaryContext binary() throws RecognitionException {
    BinaryContext local_ctx = new BinaryContext(_ctx, getState());
    enterRule(local_ctx, 20, RULEbinary);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(228);
        match(Binary);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StringContext extends ParserRuleContext {
    public TerminalNode String() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.String, 0);
    }

    public StringContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEstring;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterString(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitString(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitString(this);
      else return visitor.visitChildren(this);
    }
  }

  public final StringContext string() throws RecognitionException {
    StringContext local_ctx = new StringContext(_ctx, getState());
    enterRule(local_ctx, 22, RULEstring);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(230);
        match(String);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FloatingpointContext extends ParserRuleContext {
    public TerminalNode FloatingPoint() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.FloatingPoint, 0);
    }

    public FloatingpointContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEfloatingpoint;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterFloatingpoint(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitFloatingpoint(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFloatingpoint(this);
      else return visitor.visitChildren(this);
    }
  }

  public final FloatingpointContext floatingpoint() throws RecognitionException {
    FloatingpointContext local_ctx = new FloatingpointContext(_ctx, getState());
    enterRule(local_ctx, 24, RULEfloatingpoint);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(232);
        match(FloatingPoint);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class KeywordContext extends ParserRuleContext {
    public KeywordContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEkeyword;
    }

    public KeywordContext() {}

    public void copyFrom(KeywordContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class KeysimsymbContext extends KeywordContext {
    public TerminalNode Colon() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.Colon, 0);
    }

    public SimpleSymbolContext simpleSymbol() {
      return getRuleContext(SimpleSymbolContext.class, 0);
    }

    public KeysimsymbContext(KeywordContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterKeysimsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitKeysimsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitKeysimsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PrekeyContext extends KeywordContext {
    public PredefKeywordContext predefKeyword() {
      return getRuleContext(PredefKeywordContext.class, 0);
    }

    public PrekeyContext(KeywordContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPrekey(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPrekey(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPrekey(this);
      else return visitor.visitChildren(this);
    }
  }

  public final KeywordContext keyword() throws RecognitionException {
    KeywordContext local_ctx = new KeywordContext(_ctx, getState());
    enterRule(local_ctx, 26, RULEkeyword);
    try {
      setState(237);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case PKAllStatistics:
        case PKAssertionStackLevels:
        case PKAuthors:
        case PKCategory:
        case PKChainable:
        case PKDefinition:
        case PKDiagnosticOutputChannel:
        case PKErrorBehaviour:
        case PKExtension:
        case PKFuns:
        case PKFunsDescription:
        case PKGlobalDeclarations:
        case PKInteractiveMode:
        case PKLanguage:
        case PKLeftAssoc:
        case PKLicense:
        case PKNamed:
        case PKName:
        case PKNotes:
        case PKPattern:
        case PKPrintSuccess:
        case PKProduceAssertions:
        case PKProduceAssignments:
        case PKProduceModels:
        case PKProduceProofs:
        case PKProduceUnsatAssumptions:
        case PKProduceUnsatCores:
        case PKRandomSeed:
        case PKReasonUnknown:
        case PKRegularOutputChannel:
        case PKReproducibleResourceLimit:
        case PKRightAssoc:
        case PKSmtLibVersion:
        case PKSorts:
        case PKSortsDescription:
        case PKSource:
        case PKStatus:
        case PKTheories:
        case PKValues:
        case PKVerbosity:
        case PKVersion:
          local_ctx = new PrekeyContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(234);
            predefKeyword();
          }
          break;
        case Colon:
          local_ctx = new KeysimsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(235);
            match(Colon);
            setState(236);
            simpleSymbol();
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantContext extends ParserRuleContext {
    public SpecconstantContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEspecconstant;
    }

    public SpecconstantContext() {}

    public void copyFrom(SpecconstantContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstanthexContext extends SpecconstantContext {
    public HexadecimalContext hexadecimal() {
      return getRuleContext(HexadecimalContext.class, 0);
    }

    public SpecconstanthexContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstanthex(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstanthex(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstanthex(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantfloatingpointContext extends SpecconstantContext {
    public FloatingpointContext floatingpoint() {
      return getRuleContext(FloatingpointContext.class, 0);
    }

    public SpecconstantfloatingpointContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstantfloatingpoint(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstantfloatingpoint(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstantfloatingpoint(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantbinContext extends SpecconstantContext {
    public BinaryContext binary() {
      return getRuleContext(BinaryContext.class, 0);
    }

    public SpecconstantbinContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstantbin(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstantbin(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstantbin(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantnumContext extends SpecconstantContext {
    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public SpecconstantnumContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstantnum(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstantnum(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstantnum(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantdecContext extends SpecconstantContext {
    public DecimalContext decimal() {
      return getRuleContext(DecimalContext.class, 0);
    }

    public SpecconstantdecContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstantdec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstantdec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstantdec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecconstantstringContext extends SpecconstantContext {
    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public SpecconstantstringContext(SpecconstantContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSpecconstantstring(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSpecconstantstring(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSpecconstantstring(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SpecconstantContext specconstant() throws RecognitionException {
    SpecconstantContext local_ctx = new SpecconstantContext(_ctx, getState());
    enterRule(local_ctx, 28, RULEspecconstant);
    try {
      setState(245);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case Numeral:
          local_ctx = new SpecconstantnumContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(239);
            numeral();
          }
          break;
        case Decimal:
          local_ctx = new SpecconstantdecContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(240);
            decimal();
          }
          break;
        case HexDecimal:
          local_ctx = new SpecconstanthexContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(241);
            hexadecimal();
          }
          break;
        case Binary:
          local_ctx = new SpecconstantbinContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(242);
            binary();
          }
          break;
        case String:
          local_ctx = new SpecconstantstringContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(243);
            string();
          }
          break;
        case FloatingPoint:
          local_ctx = new SpecconstantfloatingpointContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(244);
            floatingpoint();
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SexprContext extends ParserRuleContext {
    public SexprContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsexpr;
    }

    public SexprContext() {}

    public void copyFrom(SexprContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SexprspecContext extends SexprContext {
    public SpecconstantContext specconstant() {
      return getRuleContext(SpecconstantContext.class, 0);
    }

    public SexprspecContext(SexprContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSexprspec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSexprspec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSexprspec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SexprsymbContext extends SexprContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SexprsymbContext(SexprContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSexprsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSexprsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSexprsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SexprkeyContext extends SexprContext {
    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public SexprkeyContext(SexprContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSexprkey(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSexprkey(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSexprkey(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MultisexprContext extends SexprContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SexprContext> sexpr() {
      return getRuleContexts(SexprContext.class);
    }

    public SexprContext sexpr(int i) {
      return getRuleContext(SexprContext.class, i);
    }

    public MultisexprContext(SexprContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterMultisexpr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitMultisexpr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMultisexpr(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SexprContext sexpr() throws RecognitionException {
    SexprContext local_ctx = new SexprContext(_ctx, getState());
    enterRule(local_ctx, 30, RULEsexpr);
    int la;
    try {
      setState(258);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case String:
        case Numeral:
        case Binary:
        case HexDecimal:
        case Decimal:
        case FloatingPoint:
          local_ctx = new SexprspecContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(247);
            specconstant();
          }
          break;
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new SexprsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(248);
            symbol();
          }
          break;
        case Colon:
        case PKAllStatistics:
        case PKAssertionStackLevels:
        case PKAuthors:
        case PKCategory:
        case PKChainable:
        case PKDefinition:
        case PKDiagnosticOutputChannel:
        case PKErrorBehaviour:
        case PKExtension:
        case PKFuns:
        case PKFunsDescription:
        case PKGlobalDeclarations:
        case PKInteractiveMode:
        case PKLanguage:
        case PKLeftAssoc:
        case PKLicense:
        case PKNamed:
        case PKName:
        case PKNotes:
        case PKPattern:
        case PKPrintSuccess:
        case PKProduceAssertions:
        case PKProduceAssignments:
        case PKProduceModels:
        case PKProduceProofs:
        case PKProduceUnsatAssumptions:
        case PKProduceUnsatCores:
        case PKRandomSeed:
        case PKReasonUnknown:
        case PKRegularOutputChannel:
        case PKReproducibleResourceLimit:
        case PKRightAssoc:
        case PKSmtLibVersion:
        case PKSorts:
        case PKSortsDescription:
        case PKSource:
        case PKStatus:
        case PKTheories:
        case PKValues:
        case PKVerbosity:
        case PKVersion:
          local_ctx = new SexprkeyContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(249);
            keyword();
          }
          break;
        case ParOpen:
          local_ctx = new MultisexprContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(250);
            match(ParOpen);
            setState(254);
            _errHandler.sync(this);
            la = _input.LA(1);
            while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
                || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 216172782113775631L) != 0)) {
              {
                {
                  setState(251);
                  sexpr();
                }
              }
              setState(256);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(257);
            match(ParClose);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IndexContext extends ParserRuleContext {
    public IndexContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEindex;
    }

    public IndexContext() {}

    public void copyFrom(IndexContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IdxsymbContext extends IndexContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public IdxsymbContext(IndexContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterIdxsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitIdxsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitIdxsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IdxnumContext extends IndexContext {
    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public IdxnumContext(IndexContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterIdxnum(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitIdxnum(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitIdxnum(this);
      else return visitor.visitChildren(this);
    }
  }

  public final IndexContext index() throws RecognitionException {
    IndexContext local_ctx = new IndexContext(_ctx, getState());
    enterRule(local_ctx, 32, RULEindex);
    try {
      setState(262);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case Numeral:
          local_ctx = new IdxnumContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(260);
            numeral();
          }
          break;
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new IdxsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(261);
            symbol();
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IdentifierContext extends ParserRuleContext {
    public IdentifierContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEidentifier;
    }

    public IdentifierContext() {}

    public void copyFrom(IdentifierContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IdsymbidxContext extends IdentifierContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode GRWUnderscore() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWUnderscore, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<IndexContext> index() {
      return getRuleContexts(IndexContext.class);
    }

    public IndexContext index(int i) {
      return getRuleContext(IndexContext.class, i);
    }

    public IdsymbidxContext(IdentifierContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterIdsymbidx(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitIdsymbidx(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitIdsymbidx(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IdsymbContext extends IdentifierContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public IdsymbContext(IdentifierContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterIdsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitIdsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitIdsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final IdentifierContext identifier() throws RecognitionException {
    IdentifierContext local_ctx = new IdentifierContext(_ctx, getState());
    enterRule(local_ctx, 34, RULEidentifier);
    int la;
    try {
      setState(275);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new IdsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(264);
            symbol();
          }
          break;
        case ParOpen:
          local_ctx = new IdsymbidxContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(265);
            match(ParOpen);
            setState(266);
            match(GRWUnderscore);
            setState(267);
            symbol();
            setState(269);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(268);
                  index();
                }
              }
              setState(271);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0)
                || la == Numeral
                || la == UndefinedSymbol);
            setState(273);
            match(ParClose);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttributevalueContext extends ParserRuleContext {
    public AttributevalueContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEattributevalue;
    }

    public AttributevalueContext() {}

    public void copyFrom(AttributevalueContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttrsexprContext extends AttributevalueContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SexprContext> sexpr() {
      return getRuleContexts(SexprContext.class);
    }

    public SexprContext sexpr(int i) {
      return getRuleContext(SexprContext.class, i);
    }

    public AttrsexprContext(AttributevalueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAttrsexpr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAttrsexpr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAttrsexpr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttrspecContext extends AttributevalueContext {
    public SpecconstantContext specconstant() {
      return getRuleContext(SpecconstantContext.class, 0);
    }

    public AttrspecContext(AttributevalueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAttrspec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAttrspec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAttrspec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttrsymbContext extends AttributevalueContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public AttrsymbContext(AttributevalueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAttrsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAttrsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAttrsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final AttributevalueContext attributevalue() throws RecognitionException {
    AttributevalueContext local_ctx = new AttributevalueContext(_ctx, getState());
    enterRule(local_ctx, 36, RULEattributevalue);
    int la;
    try {
      setState(287);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case String:
        case Numeral:
        case Binary:
        case HexDecimal:
        case Decimal:
        case FloatingPoint:
          local_ctx = new AttrspecContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(277);
            specconstant();
          }
          break;
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new AttrsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(278);
            symbol();
          }
          break;
        case ParOpen:
          local_ctx = new AttrsexprContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(279);
            match(ParOpen);
            setState(283);
            _errHandler.sync(this);
            la = _input.LA(1);
            while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
                || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 216172782113775631L) != 0)) {
              {
                {
                  setState(280);
                  sexpr();
                }
              }
              setState(285);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(286);
            match(ParClose);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttributeContext extends ParserRuleContext {
    public AttributeContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEattribute;
    }

    public AttributeContext() {}

    public void copyFrom(AttributeContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttrkeyattrContext extends AttributeContext {
    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public AttributevalueContext attributevalue() {
      return getRuleContext(AttributevalueContext.class, 0);
    }

    public AttrkeyattrContext(AttributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterAttrkeyattr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAttrkeyattr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAttrkeyattr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttrkeyContext extends AttributeContext {
    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public AttrkeyContext(AttributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAttrkey(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAttrkey(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAttrkey(this);
      else return visitor.visitChildren(this);
    }
  }

  public final AttributeContext attribute() throws RecognitionException {
    AttributeContext local_ctx = new AttributeContext(_ctx, getState());
    enterRule(local_ctx, 38, RULEattribute);
    try {
      setState(293);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 12, _ctx)) {
        case 1:
          local_ctx = new AttrkeyContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(289);
            keyword();
          }
          break;
        case 2:
          local_ctx = new AttrkeyattrContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(290);
            keyword();
            setState(291);
            attributevalue();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortContext extends ParserRuleContext {
    public SortContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsort;
    }

    public SortContext() {}

    public void copyFrom(SortContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MultisortContext extends SortContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public MultisortContext(SortContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterMultisort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitMultisort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMultisort(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortidContext extends SortContext {
    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public SortidContext(SortContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSortid(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSortid(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSortid(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortContext sort() throws RecognitionException {
    SortContext local_ctx = new SortContext(_ctx, getState());
    enterRule(local_ctx, 40, RULEsort);
    int la;
    try {
      setState(305);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 14, _ctx)) {
        case 1:
          local_ctx = new SortidContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(295);
            identifier();
          }
          break;
        case 2:
          local_ctx = new MultisortContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(296);
            match(ParOpen);
            setState(297);
            identifier();
            setState(299);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(298);
                  sort();
                }
              }
              setState(301);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388548L) != 0)
                || la == UndefinedSymbol);
            setState(303);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QualidentiferContext extends ParserRuleContext {
    public QualidentiferContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEqualidentifer;
    }

    public QualidentiferContext() {}

    public void copyFrom(QualidentiferContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QualidsortContext extends QualidentiferContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode GRWAs() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWAs, 0);
    }

    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public QualidsortContext(QualidentiferContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterQualidsort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitQualidsort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitQualidsort(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QualidContext extends QualidentiferContext {
    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public QualidContext(QualidentiferContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterQualid(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitQualid(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitQualid(this);
      else return visitor.visitChildren(this);
    }
  }

  public final QualidentiferContext qualidentifer() throws RecognitionException {
    QualidentiferContext local_ctx = new QualidentiferContext(_ctx, getState());
    enterRule(local_ctx, 42, RULEqualidentifer);
    try {
      setState(314);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 15, _ctx)) {
        case 1:
          local_ctx = new QualidContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(307);
            identifier();
          }
          break;
        case 2:
          local_ctx = new QualidsortContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(308);
            match(ParOpen);
            setState(309);
            match(GRWAs);
            setState(310);
            identifier();
            setState(311);
            sort();
            setState(312);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class VarbindingContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public VarbindingContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEvarbinding;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterVarbinding(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitVarbinding(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitVarbinding(this);
      else return visitor.visitChildren(this);
    }
  }

  public final VarbindingContext varbinding() throws RecognitionException {
    VarbindingContext local_ctx = new VarbindingContext(_ctx, getState());
    enterRule(local_ctx, 44, RULEvarbinding);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(316);
        match(ParOpen);
        setState(317);
        symbol();
        setState(318);
        term();
        setState(319);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortedvarContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SortedvarContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsortedvar;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSortedvar(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSortedvar(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSortedvar(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortedvarContext sortedvar() throws RecognitionException {
    SortedvarContext local_ctx = new SortedvarContext(_ctx, getState());
    enterRule(local_ctx, 46, RULEsortedvar);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(321);
        match(ParOpen);
        setState(322);
        symbol();
        setState(323);
        sort();
        setState(324);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PatternContext extends ParserRuleContext {
    public PatternContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEpattern;
    }

    public PatternContext() {}

    public void copyFrom(PatternContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PatternsymbContext extends PatternContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public PatternsymbContext(PatternContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterPatternsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPatternsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPatternsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PatternmultisymbContext extends PatternContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public PatternmultisymbContext(PatternContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterPatternmultisymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitPatternmultisymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPatternmultisymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PatternContext pattern() throws RecognitionException {
    PatternContext local_ctx = new PatternContext(_ctx, getState());
    enterRule(local_ctx, 48, RULEpattern);
    int la;
    try {
      setState(336);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new PatternsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(326);
            symbol();
          }
          break;
        case ParOpen:
          local_ctx = new PatternmultisymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(327);
            match(ParOpen);
            setState(328);
            symbol();
            setState(330);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(329);
                  symbol();
                }
              }
              setState(332);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0)
                || la == UndefinedSymbol);
            setState(334);
            match(ParClose);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MatchcaseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public PatternContext pattern() {
      return getRuleContext(PatternContext.class, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public MatchcaseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEmatchcase;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterMatchcase(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitMatchcase(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMatchcase(this);
      else return visitor.visitChildren(this);
    }
  }

  public final MatchcaseContext matchcase() throws RecognitionException {
    MatchcaseContext local_ctx = new MatchcaseContext(_ctx, getState());
    enterRule(local_ctx, 50, RULEmatchcase);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(338);
        match(ParOpen);
        setState(339);
        pattern();
        setState(340);
        term();
        setState(341);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermContext extends ParserRuleContext {
    public TermContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEterm;
    }

    public TermContext() {}

    public void copyFrom(TermContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermexistsContext extends TermContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWExists() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWExists, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public List<SortedvarContext> sortedvar() {
      return getRuleContexts(SortedvarContext.class);
    }

    public SortedvarContext sortedvar(int i) {
      return getRuleContext(SortedvarContext.class, i);
    }

    public TermexistsContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermexists(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermexists(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermexists(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MultitermContext extends TermContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public QualidentiferContext qualidentifer() {
      return getRuleContext(QualidentiferContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<TermContext> term() {
      return getRuleContexts(TermContext.class);
    }

    public TermContext term(int i) {
      return getRuleContext(TermContext.class, i);
    }

    public MultitermContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterMultiterm(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitMultiterm(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMultiterm(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermforallContext extends TermContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWForall() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWForall, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public List<SortedvarContext> sortedvar() {
      return getRuleContexts(SortedvarContext.class);
    }

    public SortedvarContext sortedvar(int i) {
      return getRuleContext(SortedvarContext.class, i);
    }

    public TermforallContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermforall(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermforall(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermforall(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermqualidContext extends TermContext {
    public QualidentiferContext qualidentifer() {
      return getRuleContext(QualidentiferContext.class, 0);
    }

    public TermqualidContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermqualid(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermqualid(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermqualid(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermspecconstContext extends TermContext {
    public SpecconstantContext specconstant() {
      return getRuleContext(SpecconstantContext.class, 0);
    }

    public TermspecconstContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterTermspecconst(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitTermspecconst(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermspecconst(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermletContext extends TermContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWLet() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWLet, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public List<VarbindingContext> varbinding() {
      return getRuleContexts(VarbindingContext.class);
    }

    public VarbindingContext varbinding(int i) {
      return getRuleContext(VarbindingContext.class, i);
    }

    public TermletContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermlet(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermlet(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermlet(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermmatchContext extends TermContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWMatch() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWMatch, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public List<MatchcaseContext> matchcase() {
      return getRuleContexts(MatchcaseContext.class);
    }

    public MatchcaseContext matchcase(int i) {
      return getRuleContext(MatchcaseContext.class, i);
    }

    public TermmatchContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermmatch(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermmatch(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermmatch(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TermexclamContext extends TermContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode GRWExclamation() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWExclamation, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public TermexclamContext(TermContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTermexclam(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTermexclam(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTermexclam(this);
      else return visitor.visitChildren(this);
    }
  }

  public final TermContext term() throws RecognitionException {
    TermContext local_ctx = new TermContext(_ctx, getState());
    enterRule(local_ctx, 52, RULEterm);
    int la;
    try {
      setState(412);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 24, _ctx)) {
        case 1:
          local_ctx = new TermspecconstContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(343);
            specconstant();
          }
          break;
        case 2:
          local_ctx = new TermqualidContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(344);
            qualidentifer();
          }
          break;
        case 3:
          local_ctx = new MultitermContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(345);
            match(ParOpen);
            setState(346);
            qualidentifer();
            setState(348);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(347);
                  term();
                }
              }
              setState(350);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
                || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 144115188075864079L) != 0));
            setState(352);
            match(ParClose);
          }
          break;
        case 4:
          local_ctx = new TermletContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(354);
            match(ParOpen);
            setState(355);
            match(GRWLet);
            setState(356);
            match(ParOpen);
            setState(358);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(357);
                  varbinding();
                }
              }
              setState(360);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(362);
            match(ParClose);
            setState(363);
            term();
            setState(364);
            match(ParClose);
          }
          break;
        case 5:
          local_ctx = new TermforallContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(366);
            match(ParOpen);
            setState(367);
            match(GRWForall);
            setState(368);
            match(ParOpen);
            setState(370);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(369);
                  sortedvar();
                }
              }
              setState(372);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(374);
            match(ParClose);
            setState(375);
            term();
            setState(376);
            match(ParClose);
          }
          break;
        case 6:
          local_ctx = new TermexistsContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(378);
            match(ParOpen);
            setState(379);
            match(GRWExists);
            setState(380);
            match(ParOpen);
            setState(382);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(381);
                  sortedvar();
                }
              }
              setState(384);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(386);
            match(ParClose);
            setState(387);
            term();
            setState(388);
            match(ParClose);
          }
          break;
        case 7:
          local_ctx = new TermmatchContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(390);
            match(ParOpen);
            setState(391);
            match(GRWMatch);
            setState(392);
            term();
            setState(393);
            match(ParOpen);
            setState(395);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(394);
                  matchcase();
                }
              }
              setState(397);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(399);
            match(ParClose);
            setState(400);
            match(ParClose);
          }
          break;
        case 8:
          local_ctx = new TermexclamContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(402);
            match(ParOpen);
            setState(403);
            match(GRWExclamation);
            setState(404);
            term();
            setState(406);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(405);
                  attribute();
                }
              }
              setState(408);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0));
            setState(410);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortsymboldeclContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public SortsymboldeclContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsortsymboldecl;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSortsymboldecl(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitSortsymboldecl(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSortsymboldecl(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortsymboldeclContext sortsymboldecl() throws RecognitionException {
    SortsymboldeclContext local_ctx = new SortsymboldeclContext(_ctx, getState());
    enterRule(local_ctx, 54, RULEsortsymboldecl);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(414);
        match(ParOpen);
        setState(415);
        identifier();
        setState(416);
        numeral();
        setState(420);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0)) {
          {
            {
              setState(417);
              attribute();
            }
          }
          setState(422);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(423);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MetaspecconstantContext extends ParserRuleContext {
    public TerminalNode GRWNumeral() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWNumeral, 0);
    }

    public TerminalNode GRWDecimal() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWDecimal, 0);
    }

    public TerminalNode GRWString() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWString, 0);
    }

    public MetaspecconstantContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEmetaspecconstant;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterMetaspecconstant(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitMetaspecconstant(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMetaspecconstant(this);
      else return visitor.visitChildren(this);
    }
  }

  public final MetaspecconstantContext metaspecconstant() throws RecognitionException {
    MetaspecconstantContext local_ctx = new MetaspecconstantContext(_ctx, getState());
    enterRule(local_ctx, 56, RULEmetaspecconstant);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(425);
        la = _input.LA(1);
        if (!(((((la - 57)) & ~0x3f) == 0 && ((1L << (la - 57)) & 321L) != 0))) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunsymboldeclContext extends ParserRuleContext {
    public FunsymboldeclContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEfunsymboldecl;
    }

    public FunsymboldeclContext() {}

    public void copyFrom(FunsymboldeclContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunsymbidContext extends FunsymboldeclContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public FunsymbidContext(FunsymboldeclContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterFunsymbid(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitFunsymbid(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFunsymbid(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunsymbspecContext extends FunsymboldeclContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SpecconstantContext specconstant() {
      return getRuleContext(SpecconstantContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public FunsymbspecContext(FunsymboldeclContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterFunsymbspec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitFunsymbspec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFunsymbspec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunsymbmetaContext extends FunsymboldeclContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public MetaspecconstantContext metaspecconstant() {
      return getRuleContext(MetaspecconstantContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public FunsymbmetaContext(FunsymboldeclContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterFunsymbmeta(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitFunsymbmeta(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFunsymbmeta(this);
      else return visitor.visitChildren(this);
    }
  }

  public final FunsymboldeclContext funsymboldecl() throws RecognitionException {
    FunsymboldeclContext local_ctx = new FunsymboldeclContext(_ctx, getState());
    enterRule(local_ctx, 58, RULEfunsymboldecl);
    int la;
    try {
      setState(464);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 30, _ctx)) {
        case 1:
          local_ctx = new FunsymbspecContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(427);
            match(ParOpen);
            setState(428);
            specconstant();
            setState(429);
            sort();
            setState(433);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0)) {
              {
                {
                  setState(430);
                  attribute();
                }
              }
              setState(435);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(436);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new FunsymbmetaContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(438);
            match(ParOpen);
            setState(439);
            metaspecconstant();
            setState(440);
            sort();
            setState(444);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0)) {
              {
                {
                  setState(441);
                  attribute();
                }
              }
              setState(446);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(447);
            match(ParClose);
          }
          break;
        case 3:
          local_ctx = new FunsymbidContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(449);
            match(ParOpen);
            setState(450);
            identifier();
            setState(452);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(451);
                  sort();
                }
              }
              setState(454);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388548L) != 0)
                || la == UndefinedSymbol);
            setState(459);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0)) {
              {
                {
                  setState(456);
                  attribute();
                }
              }
              setState(461);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(462);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ParfunsymboldeclContext extends ParserRuleContext {
    public ParfunsymboldeclContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEparfunsymboldecl;
    }

    public ParfunsymboldeclContext() {}

    public void copyFrom(ParfunsymboldeclContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ParfunsymbContext extends ParfunsymboldeclContext {
    public FunsymboldeclContext funsymboldecl() {
      return getRuleContext(FunsymboldeclContext.class, 0);
    }

    public ParfunsymbContext(ParfunsymboldeclContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterParfunsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitParfunsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitParfunsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ParfunmultisymbContext extends ParfunsymboldeclContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWPar() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWPar, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public IdentifierContext identifier() {
      return getRuleContext(IdentifierContext.class, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public ParfunmultisymbContext(ParfunsymboldeclContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterParfunmultisymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitParfunmultisymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitParfunmultisymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ParfunsymboldeclContext parfunsymboldecl() throws RecognitionException {
    ParfunsymboldeclContext local_ctx = new ParfunsymboldeclContext(_ctx, getState());
    enterRule(local_ctx, 60, RULEparfunsymboldecl);
    int la;
    try {
      setState(492);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 34, _ctx)) {
        case 1:
          local_ctx = new ParfunsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(466);
            funsymboldecl();
          }
          break;
        case 2:
          local_ctx = new ParfunmultisymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(467);
            match(ParOpen);
            setState(468);
            match(GRWPar);
            setState(469);
            match(ParOpen);
            setState(471);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(470);
                  symbol();
                }
              }
              setState(473);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0)
                || la == UndefinedSymbol);
            setState(475);
            match(ParClose);
            setState(476);
            match(ParOpen);
            setState(477);
            identifier();
            setState(479);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(478);
                  sort();
                }
              }
              setState(481);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388548L) != 0)
                || la == UndefinedSymbol);
            setState(486);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0)) {
              {
                {
                  setState(483);
                  attribute();
                }
              }
              setState(488);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(489);
            match(ParClose);
            setState(490);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheoryattributeContext extends ParserRuleContext {
    public TheoryattributeContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEtheoryattribute;
    }

    public TheoryattributeContext() {}

    public void copyFrom(TheoryattributeContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheorysortContext extends TheoryattributeContext {
    public TerminalNode PKSorts() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSorts, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SortsymboldeclContext> sortsymboldecl() {
      return getRuleContexts(SortsymboldeclContext.class);
    }

    public SortsymboldeclContext sortsymboldecl(int i) {
      return getRuleContext(SortsymboldeclContext.class, i);
    }

    public TheorysortContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheorysort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheorysort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheorysort(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheorynotesContext extends TheoryattributeContext {
    public TerminalNode PKNotes() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKNotes, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TheorynotesContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterTheorynotes(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheorynotes(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheorynotes(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheorydefContext extends TheoryattributeContext {
    public TerminalNode PKDefinition() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKDefinition, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TheorydefContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheorydef(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheorydef(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheorydef(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheoryfunContext extends TheoryattributeContext {
    public TerminalNode PKFuns() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKFuns, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<ParfunsymboldeclContext> parfunsymboldecl() {
      return getRuleContexts(ParfunsymboldeclContext.class);
    }

    public ParfunsymboldeclContext parfunsymboldecl(int i) {
      return getRuleContext(ParfunsymboldeclContext.class, i);
    }

    public TheoryfunContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheoryfun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheoryfun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheoryfun(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheoryattrContext extends TheoryattributeContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public TheoryattrContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheoryattr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheoryattr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheoryattr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheoryvalContext extends TheoryattributeContext {
    public TerminalNode PKValues() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKValues, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TheoryvalContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheoryval(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheoryval(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheoryval(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheorysortdescrContext extends TheoryattributeContext {
    public TerminalNode PKSortsDescription() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKSortsDescription, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TheorysortdescrContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterTheorysortdescr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitTheorysortdescr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheorysortdescr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheoryfundescrContext extends TheoryattributeContext {
    public TerminalNode PKFunsDescription() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKFunsDescription, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TheoryfundescrContext(TheoryattributeContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterTheoryfundescr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitTheoryfundescr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheoryfundescr(this);
      else return visitor.visitChildren(this);
    }
  }

  public final TheoryattributeContext theoryattribute() throws RecognitionException {
    TheoryattributeContext local_ctx = new TheoryattributeContext(_ctx, getState());
    enterRule(local_ctx, 62, RULEtheoryattribute);
    int la;
    try {
      setState(523);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 37, _ctx)) {
        case 1:
          local_ctx = new TheorysortContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(494);
            match(PKSorts);
            setState(495);
            match(ParOpen);
            setState(497);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(496);
                  sortsymboldecl();
                }
              }
              setState(499);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(501);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new TheoryfunContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(503);
            match(PKFuns);
            setState(504);
            match(ParOpen);
            setState(506);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(505);
                  parfunsymboldecl();
                }
              }
              setState(508);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(510);
            match(ParClose);
          }
          break;
        case 3:
          local_ctx = new TheorysortdescrContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(512);
            match(PKSortsDescription);
            setState(513);
            string();
          }
          break;
        case 4:
          local_ctx = new TheoryfundescrContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(514);
            match(PKFunsDescription);
            setState(515);
            string();
          }
          break;
        case 5:
          local_ctx = new TheorydefContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(516);
            match(PKDefinition);
            setState(517);
            string();
          }
          break;
        case 6:
          local_ctx = new TheoryvalContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(518);
            match(PKValues);
            setState(519);
            string();
          }
          break;
        case 7:
          local_ctx = new TheorynotesContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(520);
            match(PKNotes);
            setState(521);
            string();
          }
          break;
        case 8:
          local_ctx = new TheoryattrContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(522);
            attribute();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TheorydeclContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode PSTheory() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSTheory, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<TheoryattributeContext> theoryattribute() {
      return getRuleContexts(TheoryattributeContext.class);
    }

    public TheoryattributeContext theoryattribute(int i) {
      return getRuleContext(TheoryattributeContext.class, i);
    }

    public TheorydeclContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEtheorydecl;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterTheorydecl(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitTheorydecl(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTheorydecl(this);
      else return visitor.visitChildren(this);
    }
  }

  public final TheorydeclContext theorydecl() throws RecognitionException {
    TheorydeclContext local_ctx = new TheorydeclContext(_ctx, getState());
    enterRule(local_ctx, 64, RULEtheorydecl);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(525);
        match(ParOpen);
        setState(526);
        match(PSTheory);
        setState(527);
        symbol();
        setState(529);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(528);
              theoryattribute();
            }
          }
          setState(531);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0));
        setState(533);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicattribueContext extends ParserRuleContext {
    public LogicattribueContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULElogicattribue;
    }

    public LogicattribueContext() {}

    public void copyFrom(LogicattribueContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicvalContext extends LogicattribueContext {
    public TerminalNode PKValues() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKValues, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public LogicvalContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterLogicval(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogicval(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogicval(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicattrContext extends LogicattribueContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public LogicattrContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterLogicattr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogicattr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogicattr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogictheoryContext extends LogicattribueContext {
    public TerminalNode PKTheories() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKTheories, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public LogictheoryContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterLogictheory(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogictheory(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogictheory(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogiclanguageContext extends LogicattribueContext {
    public TerminalNode PKLanguage() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKLanguage, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public LogiclanguageContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterLogiclanguage(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitLogiclanguage(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogiclanguage(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicextContext extends LogicattribueContext {
    public TerminalNode PKExtension() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKExtension, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public LogicextContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterLogicext(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogicext(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogicext(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicnotesContext extends LogicattribueContext {
    public TerminalNode PKNotes() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKNotes, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public LogicnotesContext(LogicattribueContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterLogicnotes(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogicnotes(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogicnotes(this);
      else return visitor.visitChildren(this);
    }
  }

  public final LogicattribueContext logicattribue() throws RecognitionException {
    LogicattribueContext local_ctx = new LogicattribueContext(_ctx, getState());
    enterRule(local_ctx, 66, RULElogicattribue);
    int la;
    try {
      setState(553);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 40, _ctx)) {
        case 1:
          local_ctx = new LogictheoryContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(535);
            match(PKTheories);
            setState(536);
            match(ParOpen);
            setState(538);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(537);
                  symbol();
                }
              }
              setState(540);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0)
                || la == UndefinedSymbol);
            setState(542);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new LogiclanguageContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(544);
            match(PKLanguage);
            setState(545);
            string();
          }
          break;
        case 3:
          local_ctx = new LogicextContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(546);
            match(PKExtension);
            setState(547);
            string();
          }
          break;
        case 4:
          local_ctx = new LogicvalContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(548);
            match(PKValues);
            setState(549);
            string();
          }
          break;
        case 5:
          local_ctx = new LogicnotesContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(550);
            match(PKNotes);
            setState(551);
            string();
          }
          break;
        case 6:
          local_ctx = new LogicattrContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(552);
            attribute();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LogicContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode PSLogic() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSLogic, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<LogicattribueContext> logicattribue() {
      return getRuleContexts(LogicattribueContext.class);
    }

    public LogicattribueContext logicattribue(int i) {
      return getRuleContext(LogicattribueContext.class, i);
    }

    public LogicContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULElogic;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterLogic(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitLogic(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitLogic(this);
      else return visitor.visitChildren(this);
    }
  }

  public final LogicContext logic() throws RecognitionException {
    LogicContext local_ctx = new LogicContext(_ctx, getState());
    enterRule(local_ctx, 68, RULElogic);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(555);
        match(ParOpen);
        setState(556);
        match(PSLogic);
        setState(557);
        symbol();
        setState(559);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(558);
              logicattribue();
            }
          }
          setState(561);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0));
        setState(563);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortdecContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SortdecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEsortdec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSortdec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSortdec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSortdec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortdecContext sortdec() throws RecognitionException {
    SortdecContext local_ctx = new SortdecContext(_ctx, getState());
    enterRule(local_ctx, 70, RULEsortdec);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(565);
        match(ParOpen);
        setState(566);
        symbol();
        setState(567);
        numeral();
        setState(568);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SelectordecContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SelectordecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEselectordec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterSelectordec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSelectordec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSelectordec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SelectordecContext selectordec() throws RecognitionException {
    SelectordecContext local_ctx = new SelectordecContext(_ctx, getState());
    enterRule(local_ctx, 72, RULEselectordec);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(570);
        match(ParOpen);
        setState(571);
        symbol();
        setState(572);
        sort();
        setState(573);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ConstructordecContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SelectordecContext> selectordec() {
      return getRuleContexts(SelectordecContext.class);
    }

    public SelectordecContext selectordec(int i) {
      return getRuleContext(SelectordecContext.class, i);
    }

    public ConstructordecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEconstructordec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterConstructordec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitConstructordec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitConstructordec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ConstructordecContext constructordec() throws RecognitionException {
    ConstructordecContext local_ctx = new ConstructordecContext(_ctx, getState());
    enterRule(local_ctx, 74, RULEconstructordec);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(575);
        match(ParOpen);
        setState(576);
        symbol();
        setState(580);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (la == ParOpen) {
          {
            {
              setState(577);
              selectordec();
            }
          }
          setState(582);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(583);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DatatypedecContext extends ParserRuleContext {
    public DatatypedecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEdatatypedec;
    }

    public DatatypedecContext() {}

    public void copyFrom(DatatypedecContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DatamultisymbContext extends DatatypedecContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public TerminalNode GRWPar() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.GRWPar, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public List<ConstructordecContext> constructordec() {
      return getRuleContexts(ConstructordecContext.class);
    }

    public ConstructordecContext constructordec(int i) {
      return getRuleContext(ConstructordecContext.class, i);
    }

    public DatamultisymbContext(DatatypedecContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterDatamultisymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitDatamultisymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDatamultisymb(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DataconstrContext extends DatatypedecContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<ConstructordecContext> constructordec() {
      return getRuleContexts(ConstructordecContext.class);
    }

    public ConstructordecContext constructordec(int i) {
      return getRuleContext(ConstructordecContext.class, i);
    }

    public DataconstrContext(DatatypedecContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDataconstr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDataconstr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDataconstr(this);
      else return visitor.visitChildren(this);
    }
  }

  public final DatatypedecContext datatypedec() throws RecognitionException {
    DatatypedecContext local_ctx = new DatatypedecContext(_ctx, getState());
    enterRule(local_ctx, 76, RULEdatatypedec);
    int la;
    try {
      setState(611);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 46, _ctx)) {
        case 1:
          local_ctx = new DataconstrContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(585);
            match(ParOpen);
            setState(587);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(586);
                  constructordec();
                }
              }
              setState(589);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(591);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new DatamultisymbContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(593);
            match(ParOpen);
            setState(594);
            match(GRWPar);
            setState(595);
            match(ParOpen);
            setState(597);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(596);
                  symbol();
                }
              }
              setState(599);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0)
                || la == UndefinedSymbol);
            setState(601);
            match(ParClose);
            setState(602);
            match(ParOpen);
            setState(604);
            _errHandler.sync(this);
            la = _input.LA(1);
            do {
              {
                {
                  setState(603);
                  constructordec();
                }
              }
              setState(606);
              _errHandler.sync(this);
              la = _input.LA(1);
            } while (la == ParOpen);
            setState(608);
            match(ParClose);
            setState(609);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunctiondecContext extends ParserRuleContext {
    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public List<SortedvarContext> sortedvar() {
      return getRuleContexts(SortedvarContext.class);
    }

    public SortedvarContext sortedvar(int i) {
      return getRuleContext(SortedvarContext.class, i);
    }

    public FunctiondecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEfunctiondec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterFunctiondec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitFunctiondec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFunctiondec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final FunctiondecContext functiondec() throws RecognitionException {
    FunctiondecContext local_ctx = new FunctiondecContext(_ctx, getState());
    enterRule(local_ctx, 78, RULEfunctiondec);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(613);
        match(ParOpen);
        setState(614);
        symbol();
        setState(615);
        match(ParOpen);
        setState(619);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (la == ParOpen) {
          {
            {
              setState(616);
              sortedvar();
            }
          }
          setState(621);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(622);
        match(ParClose);
        setState(623);
        sort();
        setState(624);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FunctiondefContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public List<SortedvarContext> sortedvar() {
      return getRuleContexts(SortedvarContext.class);
    }

    public SortedvarContext sortedvar(int i) {
      return getRuleContext(SortedvarContext.class, i);
    }

    public FunctiondefContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEfunctiondef;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterFunctiondef(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitFunctiondef(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitFunctiondef(this);
      else return visitor.visitChildren(this);
    }
  }

  public final FunctiondefContext functiondef() throws RecognitionException {
    FunctiondefContext local_ctx = new FunctiondefContext(_ctx, getState());
    enterRule(local_ctx, 80, RULEfunctiondef);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(626);
        symbol();
        setState(627);
        match(ParOpen);
        setState(631);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (la == ParOpen) {
          {
            {
              setState(628);
              sortedvar();
            }
          }
          setState(633);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(634);
        match(ParClose);
        setState(635);
        sort();
        setState(636);
        term();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PropliteralContext extends ParserRuleContext {
    public PropliteralContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEpropliteral;
    }

    public PropliteralContext() {}

    public void copyFrom(PropliteralContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PropnotContext extends PropliteralContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode PSNot() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSNot, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public PropnotContext(PropliteralContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPropnot(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPropnot(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPropnot(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PropsymbContext extends PropliteralContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public PropsymbContext(PropliteralContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPropsymb(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPropsymb(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPropsymb(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PropliteralContext propliteral() throws RecognitionException {
    PropliteralContext local_ctx = new PropliteralContext(_ctx, getState());
    enterRule(local_ctx, 82, RULEpropliteral);
    try {
      setState(644);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case QuotedSymbol:
        case PSNot:
        case PSBool:
        case PSContinuedExecution:
        case PSError:
        case PSFalse:
        case PSImmediateExit:
        case PSIncomplete:
        case PSLogic:
        case PSMemout:
        case PSSat:
        case PSSuccess:
        case PSTheory:
        case PSTrue:
        case PSUnknown:
        case PSUnsupported:
        case PSUnsat:
        case UndefinedSymbol:
          local_ctx = new PropsymbContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(638);
            symbol();
          }
          break;
        case ParOpen:
          local_ctx = new PropnotContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(639);
            match(ParOpen);
            setState(640);
            match(PSNot);
            setState(641);
            symbol();
            setState(642);
            match(ParClose);
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ScriptContext extends ParserRuleContext {
    public List<CommandContext> command() {
      return getRuleContexts(CommandContext.class);
    }

    public CommandContext command(int i) {
      return getRuleContext(CommandContext.class, i);
    }

    public ScriptContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEscript;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterScript(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitScript(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitScript(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ScriptContext script() throws RecognitionException {
    ScriptContext local_ctx = new ScriptContext(_ctx, getState());
    enterRule(local_ctx, 84, RULEscript);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(649);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (la == ParOpen) {
          {
            {
              setState(646);
              command();
            }
          }
          setState(651);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdassertContext extends ParserRuleContext {
    public TerminalNode CMDAssert() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDAssert, 0);
    }

    public TermContext term() {
      return getRuleContext(TermContext.class, 0);
    }

    public CmdassertContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdassert;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdassert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdassert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdassert(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdassertContext cmdassert() throws RecognitionException {
    CmdassertContext local_ctx = new CmdassertContext(_ctx, getState());
    enterRule(local_ctx, 86, RULEcmdassert);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(652);
        match(CMDAssert);
        setState(653);
        term();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdcheckSatContext extends ParserRuleContext {
    public TerminalNode CMDCheckSat() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDCheckSat, 0);
    }

    public CmdcheckSatContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdcheckSat;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdcheckSat(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdcheckSat(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdcheckSat(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdcheckSatContext cmdcheckSat() throws RecognitionException {
    CmdcheckSatContext local_ctx = new CmdcheckSatContext(_ctx, getState());
    enterRule(local_ctx, 88, RULEcmdcheckSat);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(655);
        match(CMDCheckSat);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdcheckSatAssumingContext extends ParserRuleContext {
    public TerminalNode CMDCheckSatAssuming() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDCheckSatAssuming, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<PropliteralContext> propliteral() {
      return getRuleContexts(PropliteralContext.class);
    }

    public PropliteralContext propliteral(int i) {
      return getRuleContext(PropliteralContext.class, i);
    }

    public CmdcheckSatAssumingContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdcheckSatAssuming;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdcheckSatAssuming(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdcheckSatAssuming(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdcheckSatAssuming(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdcheckSatAssumingContext cmdcheckSatAssuming() throws RecognitionException {
    CmdcheckSatAssumingContext local_ctx = new CmdcheckSatAssumingContext(_ctx, getState());
    enterRule(local_ctx, 90, RULEcmdcheckSatAssuming);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(657);
        match(CMDCheckSatAssuming);
        setState(658);
        match(ParOpen);
        setState(662);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388548L) != 0) || la == UndefinedSymbol) {
          {
            {
              setState(659);
              propliteral();
            }
          }
          setState(664);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(665);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddeclareConstContext extends ParserRuleContext {
    public TerminalNode CMDDeclareConst() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDeclareConst, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public CmddeclareConstContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddeclareConst;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddeclareConst(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddeclareConst(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddeclareConst(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddeclareConstContext cmddeclareConst() throws RecognitionException {
    CmddeclareConstContext local_ctx = new CmddeclareConstContext(_ctx, getState());
    enterRule(local_ctx, 92, RULEcmddeclareConst);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(667);
        match(CMDDeclareConst);
        setState(668);
        symbol();
        setState(669);
        sort();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddeclareDatatypeContext extends ParserRuleContext {
    public TerminalNode CMDDeclareDatatype() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDeclareDatatype, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public DatatypedecContext datatypedec() {
      return getRuleContext(DatatypedecContext.class, 0);
    }

    public CmddeclareDatatypeContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddeclareDatatype;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddeclareDatatype(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddeclareDatatype(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddeclareDatatype(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddeclareDatatypeContext cmddeclareDatatype() throws RecognitionException {
    CmddeclareDatatypeContext local_ctx = new CmddeclareDatatypeContext(_ctx, getState());
    enterRule(local_ctx, 94, RULEcmddeclareDatatype);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(671);
        match(CMDDeclareDatatype);
        setState(672);
        symbol();
        setState(673);
        datatypedec();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddeclareDatatypesContext extends ParserRuleContext {
    public TerminalNode CMDDeclareDatatypes() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDeclareDatatypes, 0);
    }

    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public List<SortdecContext> sortdec() {
      return getRuleContexts(SortdecContext.class);
    }

    public SortdecContext sortdec(int i) {
      return getRuleContext(SortdecContext.class, i);
    }

    public List<DatatypedecContext> datatypedec() {
      return getRuleContexts(DatatypedecContext.class);
    }

    public DatatypedecContext datatypedec(int i) {
      return getRuleContext(DatatypedecContext.class, i);
    }

    public CmddeclareDatatypesContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddeclareDatatypes;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddeclareDatatypes(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddeclareDatatypes(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddeclareDatatypes(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddeclareDatatypesContext cmddeclareDatatypes() throws RecognitionException {
    CmddeclareDatatypesContext local_ctx = new CmddeclareDatatypesContext(_ctx, getState());
    enterRule(local_ctx, 96, RULEcmddeclareDatatypes);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(675);
        match(CMDDeclareDatatypes);
        setState(676);
        match(ParOpen);
        setState(678);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(677);
              sortdec();
            }
          }
          setState(680);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (la == ParOpen);
        setState(682);
        match(ParClose);
        setState(683);
        match(ParOpen);
        setState(685);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(684);
              datatypedec();
            }
          }
          setState(687);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (la == ParOpen);
        setState(689);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddeclareFunContext extends ParserRuleContext {
    public TerminalNode CMDDeclareFun() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDeclareFun, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public CmddeclareFunContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddeclareFun;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddeclareFun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddeclareFun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddeclareFun(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddeclareFunContext cmddeclareFun() throws RecognitionException {
    CmddeclareFunContext local_ctx = new CmddeclareFunContext(_ctx, getState());
    enterRule(local_ctx, 98, RULEcmddeclareFun);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(691);
        match(CMDDeclareFun);
        setState(692);
        symbol();
        setState(693);
        match(ParOpen);
        setState(697);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388548L) != 0) || la == UndefinedSymbol) {
          {
            {
              setState(694);
              sort();
            }
          }
          setState(699);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(700);
        match(ParClose);
        setState(701);
        sort();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddeclareSortContext extends ParserRuleContext {
    public TerminalNode CMDDeclareSort() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDeclareSort, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public CmddeclareSortContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddeclareSort;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddeclareSort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddeclareSort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddeclareSort(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddeclareSortContext cmddeclareSort() throws RecognitionException {
    CmddeclareSortContext local_ctx = new CmddeclareSortContext(_ctx, getState());
    enterRule(local_ctx, 100, RULEcmddeclareSort);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(703);
        match(CMDDeclareSort);
        setState(704);
        symbol();
        setState(705);
        numeral();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddefineFunContext extends ParserRuleContext {
    public TerminalNode CMDDefineFun() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDefineFun, 0);
    }

    public FunctiondefContext functiondef() {
      return getRuleContext(FunctiondefContext.class, 0);
    }

    public CmddefineFunContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddefineFun;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddefineFun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddefineFun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddefineFun(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddefineFunContext cmddefineFun() throws RecognitionException {
    CmddefineFunContext local_ctx = new CmddefineFunContext(_ctx, getState());
    enterRule(local_ctx, 102, RULEcmddefineFun);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(707);
        match(CMDDefineFun);
        setState(708);
        functiondef();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddefineFunRecContext extends ParserRuleContext {
    public TerminalNode CMDDefineFunRec() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDefineFunRec, 0);
    }

    public FunctiondefContext functiondef() {
      return getRuleContext(FunctiondefContext.class, 0);
    }

    public CmddefineFunRecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddefineFunRec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddefineFunRec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddefineFunRec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddefineFunRec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddefineFunRecContext cmddefineFunRec() throws RecognitionException {
    CmddefineFunRecContext local_ctx = new CmddefineFunRecContext(_ctx, getState());
    enterRule(local_ctx, 104, RULEcmddefineFunRec);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(710);
        match(CMDDefineFunRec);
        setState(711);
        functiondef();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddefineFunsRecContext extends ParserRuleContext {
    public TerminalNode CMDDefineFunsRec() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDefineFunsRec, 0);
    }

    public List<TerminalNode> ParOpen() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen);
    }

    public TerminalNode ParOpen(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, i);
    }

    public List<TerminalNode> ParClose() {
      return getTokens(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose);
    }

    public TerminalNode ParClose(int i) {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, i);
    }

    public List<FunctiondecContext> functiondec() {
      return getRuleContexts(FunctiondecContext.class);
    }

    public FunctiondecContext functiondec(int i) {
      return getRuleContext(FunctiondecContext.class, i);
    }

    public List<TermContext> term() {
      return getRuleContexts(TermContext.class);
    }

    public TermContext term(int i) {
      return getRuleContext(TermContext.class, i);
    }

    public CmddefineFunsRecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddefineFunsRec;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddefineFunsRec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddefineFunsRec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddefineFunsRec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddefineFunsRecContext cmddefineFunsRec() throws RecognitionException {
    CmddefineFunsRecContext local_ctx = new CmddefineFunsRecContext(_ctx, getState());
    enterRule(local_ctx, 106, RULEcmddefineFunsRec);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(713);
        match(CMDDefineFunsRec);
        setState(714);
        match(ParOpen);
        setState(716);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(715);
              functiondec();
            }
          }
          setState(718);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (la == ParOpen);
        setState(720);
        match(ParClose);
        setState(721);
        match(ParOpen);
        setState(723);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(722);
              term();
            }
          }
          setState(725);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
            || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 144115188075864079L) != 0));
        setState(727);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmddefineSortContext extends ParserRuleContext {
    public TerminalNode CMDDefineSort() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDDefineSort, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public CmddefineSortContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmddefineSort;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmddefineSort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmddefineSort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmddefineSort(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmddefineSortContext cmddefineSort() throws RecognitionException {
    CmddefineSortContext local_ctx = new CmddefineSortContext(_ctx, getState());
    enterRule(local_ctx, 108, RULEcmddefineSort);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(729);
        match(CMDDefineSort);
        setState(730);
        symbol();
        setState(731);
        match(ParOpen);
        setState(735);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0) || la == UndefinedSymbol) {
          {
            {
              setState(732);
              symbol();
            }
          }
          setState(737);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(738);
        match(ParClose);
        setState(739);
        sort();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdechoContext extends ParserRuleContext {
    public TerminalNode CMDEcho() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDEcho, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public CmdechoContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdecho;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdecho(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdecho(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdecho(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdechoContext cmdecho() throws RecognitionException {
    CmdechoContext local_ctx = new CmdechoContext(_ctx, getState());
    enterRule(local_ctx, 110, RULEcmdecho);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(741);
        match(CMDEcho);
        setState(742);
        string();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdexitContext extends ParserRuleContext {
    public TerminalNode CMDExit() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDExit, 0);
    }

    public CmdexitContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdexit;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdexit(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdexit(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdexit(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdexitContext cmdexit() throws RecognitionException {
    CmdexitContext local_ctx = new CmdexitContext(_ctx, getState());
    enterRule(local_ctx, 112, RULEcmdexit);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(744);
        match(CMDExit);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetAssertionsContext extends ParserRuleContext {
    public TerminalNode CMDGetAssertions() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetAssertions, 0);
    }

    public CmdgetAssertionsContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetAssertions;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetAssertions(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdgetAssertions(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetAssertions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetAssertionsContext cmdgetAssertions() throws RecognitionException {
    CmdgetAssertionsContext local_ctx = new CmdgetAssertionsContext(_ctx, getState());
    enterRule(local_ctx, 114, RULEcmdgetAssertions);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(746);
        match(CMDGetAssertions);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetAssignmentContext extends ParserRuleContext {
    public TerminalNode CMDGetAssignment() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetAssignment, 0);
    }

    public CmdgetAssignmentContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetAssignment;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetAssignment(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdgetAssignment(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetAssignment(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetAssignmentContext cmdgetAssignment() throws RecognitionException {
    CmdgetAssignmentContext local_ctx = new CmdgetAssignmentContext(_ctx, getState());
    enterRule(local_ctx, 116, RULEcmdgetAssignment);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(748);
        match(CMDGetAssignment);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetInfoContext extends ParserRuleContext {
    public TerminalNode CMDGetInfo() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetInfo, 0);
    }

    public InfoflagContext infoflag() {
      return getRuleContext(InfoflagContext.class, 0);
    }

    public CmdgetInfoContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetInfo;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdgetInfo(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdgetInfo(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetInfo(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetInfoContext cmdgetInfo() throws RecognitionException {
    CmdgetInfoContext local_ctx = new CmdgetInfoContext(_ctx, getState());
    enterRule(local_ctx, 118, RULEcmdgetInfo);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(750);
        match(CMDGetInfo);
        setState(751);
        infoflag();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetModelContext extends ParserRuleContext {
    public TerminalNode CMDGetModel() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetModel, 0);
    }

    public CmdgetModelContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetModel;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetModel(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdgetModel(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetModel(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetModelContext cmdgetModel() throws RecognitionException {
    CmdgetModelContext local_ctx = new CmdgetModelContext(_ctx, getState());
    enterRule(local_ctx, 120, RULEcmdgetModel);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(753);
        match(CMDGetModel);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetOptionContext extends ParserRuleContext {
    public TerminalNode CMDGetOption() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetOption, 0);
    }

    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public CmdgetOptionContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetOption;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetOption(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdgetOption(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetOption(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetOptionContext cmdgetOption() throws RecognitionException {
    CmdgetOptionContext local_ctx = new CmdgetOptionContext(_ctx, getState());
    enterRule(local_ctx, 122, RULEcmdgetOption);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(755);
        match(CMDGetOption);
        setState(756);
        keyword();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetProofContext extends ParserRuleContext {
    public TerminalNode CMDGetProof() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetProof, 0);
    }

    public CmdgetProofContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetProof;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetProof(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdgetProof(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetProof(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetProofContext cmdgetProof() throws RecognitionException {
    CmdgetProofContext local_ctx = new CmdgetProofContext(_ctx, getState());
    enterRule(local_ctx, 124, RULEcmdgetProof);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(758);
        match(CMDGetProof);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetUnsatAssumptionsContext extends ParserRuleContext {
    public TerminalNode CMDGetUnsatAssumptions() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetUnsatAssumptions,
          0);
    }

    public CmdgetUnsatAssumptionsContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetUnsatAssumptions;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetUnsatAssumptions(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdgetUnsatAssumptions(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetUnsatAssumptions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetUnsatAssumptionsContext cmdgetUnsatAssumptions() throws RecognitionException {
    CmdgetUnsatAssumptionsContext local_ctx = new CmdgetUnsatAssumptionsContext(_ctx, getState());
    enterRule(local_ctx, 126, RULEcmdgetUnsatAssumptions);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(760);
        match(CMDGetUnsatAssumptions);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetUnsatCoreContext extends ParserRuleContext {
    public TerminalNode CMDGetUnsatCore() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetUnsatCore, 0);
    }

    public CmdgetUnsatCoreContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetUnsatCore;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetUnsatCore(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdgetUnsatCore(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetUnsatCore(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetUnsatCoreContext cmdgetUnsatCore() throws RecognitionException {
    CmdgetUnsatCoreContext local_ctx = new CmdgetUnsatCoreContext(_ctx, getState());
    enterRule(local_ctx, 128, RULEcmdgetUnsatCore);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(762);
        match(CMDGetUnsatCore);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdgetValueContext extends ParserRuleContext {
    public TerminalNode CMDGetValue() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDGetValue, 0);
    }

    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<TermContext> term() {
      return getRuleContexts(TermContext.class);
    }

    public TermContext term(int i) {
      return getRuleContext(TermContext.class, i);
    }

    public CmdgetValueContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdgetValue;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdgetValue(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdgetValue(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdgetValue(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdgetValueContext cmdgetValue() throws RecognitionException {
    CmdgetValueContext local_ctx = new CmdgetValueContext(_ctx, getState());
    enterRule(local_ctx, 130, RULEcmdgetValue);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(764);
        match(CMDGetValue);
        setState(765);
        match(ParOpen);
        setState(767);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(766);
              term();
            }
          }
          setState(769);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
            || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 144115188075864079L) != 0));
        setState(771);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdpopContext extends ParserRuleContext {
    public TerminalNode CMDPop() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDPop, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public CmdpopContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdpop;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdpop(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdpop(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdpop(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdpopContext cmdpop() throws RecognitionException {
    CmdpopContext local_ctx = new CmdpopContext(_ctx, getState());
    enterRule(local_ctx, 132, RULEcmdpop);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(773);
        match(CMDPop);
        setState(774);
        numeral();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdpushContext extends ParserRuleContext {
    public TerminalNode CMDPush() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDPush, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public CmdpushContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdpush;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdpush(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdpush(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdpush(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdpushContext cmdpush() throws RecognitionException {
    CmdpushContext local_ctx = new CmdpushContext(_ctx, getState());
    enterRule(local_ctx, 134, RULEcmdpush);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(776);
        match(CMDPush);
        setState(777);
        numeral();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdresetContext extends ParserRuleContext {
    public TerminalNode CMDReset() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDReset, 0);
    }

    public CmdresetContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdreset;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdreset(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdreset(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdreset(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdresetContext cmdreset() throws RecognitionException {
    CmdresetContext local_ctx = new CmdresetContext(_ctx, getState());
    enterRule(local_ctx, 136, RULEcmdreset);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(779);
        match(CMDReset);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdresetAssertionsContext extends ParserRuleContext {
    public TerminalNode CMDResetAssertions() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDResetAssertions, 0);
    }

    public CmdresetAssertionsContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdresetAssertions;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdresetAssertions(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdresetAssertions(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdresetAssertions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdresetAssertionsContext cmdresetAssertions() throws RecognitionException {
    CmdresetAssertionsContext local_ctx = new CmdresetAssertionsContext(_ctx, getState());
    enterRule(local_ctx, 138, RULEcmdresetAssertions);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(781);
        match(CMDResetAssertions);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdsetInfoContext extends ParserRuleContext {
    public TerminalNode CMDSetInfo() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDSetInfo, 0);
    }

    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public CmdsetInfoContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdsetInfo;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCmdsetInfo(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdsetInfo(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdsetInfo(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdsetInfoContext cmdsetInfo() throws RecognitionException {
    CmdsetInfoContext local_ctx = new CmdsetInfoContext(_ctx, getState());
    enterRule(local_ctx, 140, RULEcmdsetInfo);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(783);
        match(CMDSetInfo);
        setState(784);
        attribute();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdsetLogicContext extends ParserRuleContext {
    public TerminalNode CMDSetLogic() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDSetLogic, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public CmdsetLogicContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdsetLogic;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdsetLogic(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCmdsetLogic(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdsetLogic(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdsetLogicContext cmdsetLogic() throws RecognitionException {
    CmdsetLogicContext local_ctx = new CmdsetLogicContext(_ctx, getState());
    enterRule(local_ctx, 142, RULEcmdsetLogic);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(786);
        match(CMDSetLogic);
        setState(787);
        symbol();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CmdsetOptionContext extends ParserRuleContext {
    public TerminalNode CMDSetOption() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.CMDSetOption, 0);
    }

    public OptionContext option() {
      return getRuleContext(OptionContext.class, 0);
    }

    public CmdsetOptionContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcmdsetOption;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCmdsetOption(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitCmdsetOption(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCmdsetOption(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CmdsetOptionContext cmdsetOption() throws RecognitionException {
    CmdsetOptionContext local_ctx = new CmdsetOptionContext(_ctx, getState());
    enterRule(local_ctx, 144, RULEcmdsetOption);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(789);
        match(CMDSetOption);
        setState(790);
        option();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CommandContext extends ParserRuleContext {
    public CommandContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEcommand;
    }

    public CommandContext() {}

    public void copyFrom(CommandContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetmodelContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetModelContext cmdgetModel() {
      return getRuleContext(CmdgetModelContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetmodelContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetmodel(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetmodel(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetmodel(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DecldatasContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddeclareDatatypesContext cmddeclareDatatypes() {
      return getRuleContext(CmddeclareDatatypesContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DecldatasContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDecldatas(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDecldatas(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDecldatas(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeclsortContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddeclareSortContext cmddeclareSort() {
      return getRuleContext(CmddeclareSortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeclsortContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeclsort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeclsort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeclsort(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class EchoContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdechoContext cmdecho() {
      return getRuleContext(CmdechoContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public EchoContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterEcho(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitEcho(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitEcho(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetunsatassumeContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetUnsatAssumptionsContext cmdgetUnsatAssumptions() {
      return getRuleContext(CmdgetUnsatAssumptionsContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetunsatassumeContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetunsatassume(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetunsatassume(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetunsatassume(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DecldataContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddeclareDatatypeContext cmddeclareDatatype() {
      return getRuleContext(CmddeclareDatatypeContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DecldataContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDecldata(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDecldata(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDecldata(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PopContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdpopContext cmdpop() {
      return getRuleContext(CmdpopContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public PopContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPop(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPop(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPop(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DefsortContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineSortContext cmddefineSort() {
      return getRuleContext(CmddefineSortContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DefsortContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDefsort(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDefsort(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDefsort(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AssertContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdassertContext cmdassert() {
      return getRuleContext(CmdassertContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public AssertContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAssert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAssert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAssert(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeffunrecContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunRecContext cmddefineFunRec() {
      return getRuleContext(CmddefineFunRecContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeffunrecContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeffunrec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeffunrec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeffunrec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeffunContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunContext cmddefineFun() {
      return getRuleContext(CmddefineFunContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeffunContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeffun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeffun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeffun(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetassertContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetAssertionsContext cmdgetAssertions() {
      return getRuleContext(CmdgetAssertionsContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetassertContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetassert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetassert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetassert(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeclconstContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddeclareConstContext cmddeclareConst() {
      return getRuleContext(CmddeclareConstContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeclconstContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeclconst(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeclconst(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeclconst(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetlogicContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdsetLogicContext cmdsetLogic() {
      return getRuleContext(CmdsetLogicContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SetlogicContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSetlogic(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSetlogic(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSetlogic(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CheckassumeContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdcheckSatAssumingContext cmdcheckSatAssuming() {
      return getRuleContext(CmdcheckSatAssumingContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public CheckassumeContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterCheckassume(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCheckassume(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCheckassume(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResetassertContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdresetAssertionsContext cmdresetAssertions() {
      return getRuleContext(CmdresetAssertionsContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public ResetassertContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterResetassert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitResetassert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitResetassert(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CheckContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdcheckSatContext cmdcheckSat() {
      return getRuleContext(CmdcheckSatContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public CheckContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterCheck(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitCheck(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitCheck(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetassignContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetAssignmentContext cmdgetAssignment() {
      return getRuleContext(CmdgetAssignmentContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetassignContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetassign(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetassign(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetassign(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PushContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdpushContext cmdpush() {
      return getRuleContext(CmdpushContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public PushContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPush(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPush(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPush(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeffunsrecContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunsRecContext cmddefineFunsRec() {
      return getRuleContext(CmddefineFunsRecContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeffunsrecContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeffunsrec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeffunsrec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeffunsrec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ExitContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdexitContext cmdexit() {
      return getRuleContext(CmdexitContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public ExitContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterExit(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitExit(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitExit(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetoptionContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetOptionContext cmdgetOption() {
      return getRuleContext(CmdgetOptionContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetoptionContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetoption(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetoption(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetoption(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetvalContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetValueContext cmdgetValue() {
      return getRuleContext(CmdgetValueContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetvalContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetval(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetval(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetval(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetoptionContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdsetOptionContext cmdsetOption() {
      return getRuleContext(CmdsetOptionContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SetoptionContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSetoption(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSetoption(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSetoption(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeclfunContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddeclareFunContext cmddeclareFun() {
      return getRuleContext(CmddeclareFunContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public DeclfunContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDeclfun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDeclfun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDeclfun(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetproofContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetProofContext cmdgetProof() {
      return getRuleContext(CmdgetProofContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetproofContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetproof(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetproof(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetproof(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetunsatcoreContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetUnsatCoreContext cmdgetUnsatCore() {
      return getRuleContext(CmdgetUnsatCoreContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetunsatcoreContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetunsatcore(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetunsatcore(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetunsatcore(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResetContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdresetContext cmdreset() {
      return getRuleContext(CmdresetContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public ResetContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterReset(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitReset(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitReset(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetinfoContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdgetInfoContext cmdgetInfo() {
      return getRuleContext(CmdgetInfoContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public GetinfoContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGetinfo(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGetinfo(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetinfo(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetInfoContext extends CommandContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmdsetInfoContext cmdsetInfo() {
      return getRuleContext(CmdsetInfoContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public SetInfoContext(CommandContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterSetInfo(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitSetInfo(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitSetInfo(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CommandContext command() throws RecognitionException {
    CommandContext local_ctx = new CommandContext(_ctx, getState());
    enterRule(local_ctx, 146, RULEcommand);
    try {
      setState(912);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 59, _ctx)) {
        case 1:
          local_ctx = new AssertContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(792);
            match(ParOpen);
            setState(793);
            cmdassert();
            setState(794);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new CheckContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(796);
            match(ParOpen);
            setState(797);
            cmdcheckSat();
            setState(798);
            match(ParClose);
          }
          break;
        case 3:
          local_ctx = new CheckassumeContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(800);
            match(ParOpen);
            setState(801);
            cmdcheckSatAssuming();
            setState(802);
            match(ParClose);
          }
          break;
        case 4:
          local_ctx = new DeclconstContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(804);
            match(ParOpen);
            setState(805);
            cmddeclareConst();
            setState(806);
            match(ParClose);
          }
          break;
        case 5:
          local_ctx = new DecldataContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(808);
            match(ParOpen);
            setState(809);
            cmddeclareDatatype();
            setState(810);
            match(ParClose);
          }
          break;
        case 6:
          local_ctx = new DecldatasContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(812);
            match(ParOpen);
            setState(813);
            cmddeclareDatatypes();
            setState(814);
            match(ParClose);
          }
          break;
        case 7:
          local_ctx = new DeclfunContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(816);
            match(ParOpen);
            setState(817);
            cmddeclareFun();
            setState(818);
            match(ParClose);
          }
          break;
        case 8:
          local_ctx = new DeclsortContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(820);
            match(ParOpen);
            setState(821);
            cmddeclareSort();
            setState(822);
            match(ParClose);
          }
          break;
        case 9:
          local_ctx = new DeffunContext(local_ctx);
          enterOuterAlt(local_ctx, 9);
          {
            setState(824);
            match(ParOpen);
            setState(825);
            cmddefineFun();
            setState(826);
            match(ParClose);
          }
          break;
        case 10:
          local_ctx = new DeffunrecContext(local_ctx);
          enterOuterAlt(local_ctx, 10);
          {
            setState(828);
            match(ParOpen);
            setState(829);
            cmddefineFunRec();
            setState(830);
            match(ParClose);
          }
          break;
        case 11:
          local_ctx = new DeffunsrecContext(local_ctx);
          enterOuterAlt(local_ctx, 11);
          {
            setState(832);
            match(ParOpen);
            setState(833);
            cmddefineFunsRec();
            setState(834);
            match(ParClose);
          }
          break;
        case 12:
          local_ctx = new DefsortContext(local_ctx);
          enterOuterAlt(local_ctx, 12);
          {
            setState(836);
            match(ParOpen);
            setState(837);
            cmddefineSort();
            setState(838);
            match(ParClose);
          }
          break;
        case 13:
          local_ctx = new EchoContext(local_ctx);
          enterOuterAlt(local_ctx, 13);
          {
            setState(840);
            match(ParOpen);
            setState(841);
            cmdecho();
            setState(842);
            match(ParClose);
          }
          break;
        case 14:
          local_ctx = new ExitContext(local_ctx);
          enterOuterAlt(local_ctx, 14);
          {
            setState(844);
            match(ParOpen);
            setState(845);
            cmdexit();
            setState(846);
            match(ParClose);
          }
          break;
        case 15:
          local_ctx = new GetassertContext(local_ctx);
          enterOuterAlt(local_ctx, 15);
          {
            setState(848);
            match(ParOpen);
            setState(849);
            cmdgetAssertions();
            setState(850);
            match(ParClose);
          }
          break;
        case 16:
          local_ctx = new GetassignContext(local_ctx);
          enterOuterAlt(local_ctx, 16);
          {
            setState(852);
            match(ParOpen);
            setState(853);
            cmdgetAssignment();
            setState(854);
            match(ParClose);
          }
          break;
        case 17:
          local_ctx = new GetinfoContext(local_ctx);
          enterOuterAlt(local_ctx, 17);
          {
            setState(856);
            match(ParOpen);
            setState(857);
            cmdgetInfo();
            setState(858);
            match(ParClose);
          }
          break;
        case 18:
          local_ctx = new GetmodelContext(local_ctx);
          enterOuterAlt(local_ctx, 18);
          {
            setState(860);
            match(ParOpen);
            setState(861);
            cmdgetModel();
            setState(862);
            match(ParClose);
          }
          break;
        case 19:
          local_ctx = new GetoptionContext(local_ctx);
          enterOuterAlt(local_ctx, 19);
          {
            setState(864);
            match(ParOpen);
            setState(865);
            cmdgetOption();
            setState(866);
            match(ParClose);
          }
          break;
        case 20:
          local_ctx = new GetproofContext(local_ctx);
          enterOuterAlt(local_ctx, 20);
          {
            setState(868);
            match(ParOpen);
            setState(869);
            cmdgetProof();
            setState(870);
            match(ParClose);
          }
          break;
        case 21:
          local_ctx = new GetunsatassumeContext(local_ctx);
          enterOuterAlt(local_ctx, 21);
          {
            setState(872);
            match(ParOpen);
            setState(873);
            cmdgetUnsatAssumptions();
            setState(874);
            match(ParClose);
          }
          break;
        case 22:
          local_ctx = new GetunsatcoreContext(local_ctx);
          enterOuterAlt(local_ctx, 22);
          {
            setState(876);
            match(ParOpen);
            setState(877);
            cmdgetUnsatCore();
            setState(878);
            match(ParClose);
          }
          break;
        case 23:
          local_ctx = new GetvalContext(local_ctx);
          enterOuterAlt(local_ctx, 23);
          {
            setState(880);
            match(ParOpen);
            setState(881);
            cmdgetValue();
            setState(882);
            match(ParClose);
          }
          break;
        case 24:
          local_ctx = new PopContext(local_ctx);
          enterOuterAlt(local_ctx, 24);
          {
            setState(884);
            match(ParOpen);
            setState(885);
            cmdpop();
            setState(886);
            match(ParClose);
          }
          break;
        case 25:
          local_ctx = new PushContext(local_ctx);
          enterOuterAlt(local_ctx, 25);
          {
            setState(888);
            match(ParOpen);
            setState(889);
            cmdpush();
            setState(890);
            match(ParClose);
          }
          break;
        case 26:
          local_ctx = new ResetContext(local_ctx);
          enterOuterAlt(local_ctx, 26);
          {
            setState(892);
            match(ParOpen);
            setState(893);
            cmdreset();
            setState(894);
            match(ParClose);
          }
          break;
        case 27:
          local_ctx = new ResetassertContext(local_ctx);
          enterOuterAlt(local_ctx, 27);
          {
            setState(896);
            match(ParOpen);
            setState(897);
            cmdresetAssertions();
            setState(898);
            match(ParClose);
          }
          break;
        case 28:
          local_ctx = new SetInfoContext(local_ctx);
          enterOuterAlt(local_ctx, 28);
          {
            setState(900);
            match(ParOpen);
            setState(901);
            cmdsetInfo();
            setState(902);
            match(ParClose);
          }
          break;
        case 29:
          local_ctx = new SetlogicContext(local_ctx);
          enterOuterAlt(local_ctx, 29);
          {
            setState(904);
            match(ParOpen);
            setState(905);
            cmdsetLogic();
            setState(906);
            match(ParClose);
          }
          break;
        case 30:
          local_ctx = new SetoptionContext(local_ctx);
          enterOuterAlt(local_ctx, 30);
          {
            setState(908);
            match(ParOpen);
            setState(909);
            cmdsetOption();
            setState(910);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class BvalueContext extends ParserRuleContext {
    public TerminalNode PSTrue() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSTrue, 0);
    }

    public TerminalNode PSFalse() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSFalse, 0);
    }

    public BvalueContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEbvalue;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterBvalue(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitBvalue(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitBvalue(this);
      else return visitor.visitChildren(this);
    }
  }

  public final BvalueContext bvalue() throws RecognitionException {
    BvalueContext local_ctx = new BvalueContext(_ctx, getState());
    enterRule(local_ctx, 148, RULEbvalue);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(914);
        la = _input.LA(1);
        if (!(la == PSFalse || la == PSTrue)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class OptionContext extends ParserRuleContext {
    public OptionContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEoption;
    }

    public OptionContext() {}

    public void copyFrom(OptionContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RandseedContext extends OptionContext {
    public TerminalNode PKRandomSeed() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKRandomSeed, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public RandseedContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRandseed(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRandseed(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRandseed(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InteractiveContext extends OptionContext {
    public TerminalNode PKInteractiveMode() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKInteractiveMode, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public InteractiveContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterInteractive(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInteractive(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInteractive(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GlobalContext extends OptionContext {
    public TerminalNode PKGlobalDeclarations() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKGlobalDeclarations, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public GlobalContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterGlobal(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitGlobal(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGlobal(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdassertContext extends OptionContext {
    public TerminalNode PKProduceAssertions() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceAssertions, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdassertContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterProdassert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitProdassert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdassert(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class OptattrContext extends OptionContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public OptattrContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterOptattr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitOptattr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitOptattr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ReproContext extends OptionContext {
    public TerminalNode PKReproducibleResourceLimit() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKReproducibleResourceLimit,
          0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public ReproContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRepro(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRepro(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRepro(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class VerboseContext extends OptionContext {
    public TerminalNode PKVerbosity() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKVerbosity, 0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public VerboseContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterVerbose(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitVerbose(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitVerbose(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PrintsuccContext extends OptionContext {
    public TerminalNode PKPrintSuccess() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKPrintSuccess, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public PrintsuccContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterPrintsucc(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitPrintsucc(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitPrintsucc(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdassignContext extends OptionContext {
    public TerminalNode PKProduceAssignments() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceAssignments, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdassignContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterProdassign(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitProdassign(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdassign(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdunsatassumeContext extends OptionContext {
    public TerminalNode PKProduceUnsatAssumptions() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKProduceUnsatAssumptions,
          0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdunsatassumeContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterProdunsatassume(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitProdunsatassume(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdunsatassume(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdunsatcoreContext extends OptionContext {
    public TerminalNode PKProduceUnsatCores() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceUnsatCores, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdunsatcoreContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterProdunsatcore(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitProdunsatcore(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdunsatcore(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DiagnoseContext extends OptionContext {
    public TerminalNode PKDiagnosticOutputChannel() {
      return getToken(
          org.sosy_lab
              .java_smt
              .basicimpl
              .parserInterpreter
              .Smtlibv2Parser
              .PKDiagnosticOutputChannel,
          0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public DiagnoseContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterDiagnose(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitDiagnose(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitDiagnose(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdproofsContext extends OptionContext {
    public TerminalNode PKProduceProofs() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceProofs, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdproofsContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterProdproofs(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitProdproofs(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdproofs(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ProdmodContext extends OptionContext {
    public TerminalNode PKProduceModels() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKProduceModels, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public ProdmodContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterProdmod(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitProdmod(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitProdmod(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RegoutContext extends OptionContext {
    public TerminalNode PKRegularOutputChannel() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKRegularOutputChannel,
          0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public RegoutContext(OptionContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRegout(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRegout(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRegout(this);
      else return visitor.visitChildren(this);
    }
  }

  public final OptionContext option() throws RecognitionException {
    OptionContext local_ctx = new OptionContext(_ctx, getState());
    enterRule(local_ctx, 150, RULEoption);
    try {
      setState(945);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 60, _ctx)) {
        case 1:
          local_ctx = new DiagnoseContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(916);
            match(PKDiagnosticOutputChannel);
            setState(917);
            string();
          }
          break;
        case 2:
          local_ctx = new GlobalContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(918);
            match(PKGlobalDeclarations);
            setState(919);
            bvalue();
          }
          break;
        case 3:
          local_ctx = new InteractiveContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(920);
            match(PKInteractiveMode);
            setState(921);
            bvalue();
          }
          break;
        case 4:
          local_ctx = new PrintsuccContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(922);
            match(PKPrintSuccess);
            setState(923);
            bvalue();
          }
          break;
        case 5:
          local_ctx = new ProdassertContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(924);
            match(PKProduceAssertions);
            setState(925);
            bvalue();
          }
          break;
        case 6:
          local_ctx = new ProdassignContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(926);
            match(PKProduceAssignments);
            setState(927);
            bvalue();
          }
          break;
        case 7:
          local_ctx = new ProdmodContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(928);
            match(PKProduceModels);
            setState(929);
            bvalue();
          }
          break;
        case 8:
          local_ctx = new ProdproofsContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(930);
            match(PKProduceProofs);
            setState(931);
            bvalue();
          }
          break;
        case 9:
          local_ctx = new ProdunsatassumeContext(local_ctx);
          enterOuterAlt(local_ctx, 9);
          {
            setState(932);
            match(PKProduceUnsatAssumptions);
            setState(933);
            bvalue();
          }
          break;
        case 10:
          local_ctx = new ProdunsatcoreContext(local_ctx);
          enterOuterAlt(local_ctx, 10);
          {
            setState(934);
            match(PKProduceUnsatCores);
            setState(935);
            bvalue();
          }
          break;
        case 11:
          local_ctx = new RandseedContext(local_ctx);
          enterOuterAlt(local_ctx, 11);
          {
            setState(936);
            match(PKRandomSeed);
            setState(937);
            numeral();
          }
          break;
        case 12:
          local_ctx = new RegoutContext(local_ctx);
          enterOuterAlt(local_ctx, 12);
          {
            setState(938);
            match(PKRegularOutputChannel);
            setState(939);
            string();
          }
          break;
        case 13:
          local_ctx = new ReproContext(local_ctx);
          enterOuterAlt(local_ctx, 13);
          {
            setState(940);
            match(PKReproducibleResourceLimit);
            setState(941);
            numeral();
          }
          break;
        case 14:
          local_ctx = new VerboseContext(local_ctx);
          enterOuterAlt(local_ctx, 14);
          {
            setState(942);
            match(PKVerbosity);
            setState(943);
            numeral();
          }
          break;
        case 15:
          local_ctx = new OptattrContext(local_ctx);
          enterOuterAlt(local_ctx, 15);
          {
            setState(944);
            attribute();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoflagContext extends ParserRuleContext {
    public InfoflagContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEinfoflag;
    }

    public InfoflagContext() {}

    public void copyFrom(InfoflagContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RunknownContext extends InfoflagContext {
    public TerminalNode PKReasonUnknown() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKReasonUnknown, 0);
    }

    public RunknownContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRunknown(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRunknown(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRunknown(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AssertstackContext extends InfoflagContext {
    public TerminalNode PKAssertionStackLevels() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAssertionStackLevels,
          0);
    }

    public AssertstackContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterAssertstack(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAssertstack(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAssertstack(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class NameContext extends InfoflagContext {
    public TerminalNode PKName() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKName, 0);
    }

    public NameContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterName(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitName(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitName(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ErrorContext extends InfoflagContext {
    public TerminalNode PKErrorBehaviour() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKErrorBehaviour, 0);
    }

    public ErrorContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterError(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitError(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitError(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AllstatContext extends InfoflagContext {
    public TerminalNode PKAllStatistics() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAllStatistics, 0);
    }

    public AllstatContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAllstat(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAllstat(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAllstat(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class VersionContext extends InfoflagContext {
    public TerminalNode PKVersion() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKVersion, 0);
    }

    public VersionContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterVersion(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitVersion(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitVersion(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfokeyContext extends InfoflagContext {
    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public InfokeyContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterInfokey(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfokey(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfokey(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AuthorsContext extends InfoflagContext {
    public TerminalNode PKAuthors() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAuthors, 0);
    }

    public AuthorsContext(InfoflagContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterAuthors(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitAuthors(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitAuthors(this);
      else return visitor.visitChildren(this);
    }
  }

  public final InfoflagContext infoflag() throws RecognitionException {
    InfoflagContext local_ctx = new InfoflagContext(_ctx, getState());
    enterRule(local_ctx, 152, RULEinfoflag);
    try {
      setState(955);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 61, _ctx)) {
        case 1:
          local_ctx = new AllstatContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(947);
            match(PKAllStatistics);
          }
          break;
        case 2:
          local_ctx = new AssertstackContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(948);
            match(PKAssertionStackLevels);
          }
          break;
        case 3:
          local_ctx = new AuthorsContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(949);
            match(PKAuthors);
          }
          break;
        case 4:
          local_ctx = new ErrorContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(950);
            match(PKErrorBehaviour);
          }
          break;
        case 5:
          local_ctx = new NameContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(951);
            match(PKName);
          }
          break;
        case 6:
          local_ctx = new RunknownContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(952);
            match(PKReasonUnknown);
          }
          break;
        case 7:
          local_ctx = new VersionContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(953);
            match(PKVersion);
          }
          break;
        case 8:
          local_ctx = new InfokeyContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(954);
            keyword();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ErrorbehaviourContext extends ParserRuleContext {
    public TerminalNode PSImmediateExit() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSImmediateExit, 0);
    }

    public TerminalNode PSContinuedExecution() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSContinuedExecution, 0);
    }

    public ErrorbehaviourContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEerrorbehaviour;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterErrorbehaviour(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitErrorbehaviour(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitErrorbehaviour(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ErrorbehaviourContext errorbehaviour() throws RecognitionException {
    ErrorbehaviourContext local_ctx = new ErrorbehaviourContext(_ctx, getState());
    enterRule(local_ctx, 154, RULEerrorbehaviour);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(957);
        la = _input.LA(1);
        if (!(la == PSContinuedExecution || la == PSImmediateExit)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ReasonunknownContext extends ParserRuleContext {
    public ReasonunknownContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEreasonunknown;
    }

    public ReasonunknownContext() {}

    public void copyFrom(ReasonunknownContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class MemoutContext extends ReasonunknownContext {
    public TerminalNode PSMemout() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSMemout, 0);
    }

    public MemoutContext(ReasonunknownContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterMemout(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitMemout(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitMemout(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IncompContext extends ReasonunknownContext {
    public TerminalNode PSIncomplete() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSIncomplete, 0);
    }

    public IncompContext(ReasonunknownContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterIncomp(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitIncomp(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitIncomp(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RunnownsexprContext extends ReasonunknownContext {
    public SexprContext sexpr() {
      return getRuleContext(SexprContext.class, 0);
    }

    public RunnownsexprContext(ReasonunknownContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRunnownsexpr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRunnownsexpr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRunnownsexpr(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ReasonunknownContext reasonunknown() throws RecognitionException {
    ReasonunknownContext local_ctx = new ReasonunknownContext(_ctx, getState());
    enterRule(local_ctx, 156, RULEreasonunknown);
    try {
      setState(962);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 62, _ctx)) {
        case 1:
          local_ctx = new MemoutContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(959);
            match(PSMemout);
          }
          break;
        case 2:
          local_ctx = new IncompContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(960);
            match(PSIncomplete);
          }
          break;
        case 3:
          local_ctx = new RunnownsexprContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(961);
            sexpr();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ModelresponseContext extends ParserRuleContext {
    public ModelresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEmodelresponse;
    }

    public ModelresponseContext() {}

    public void copyFrom(ModelresponseContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespdeffunContext extends ModelresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunContext cmddefineFun() {
      return getRuleContext(CmddefineFunContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public RespdeffunContext(ModelresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRespdeffun(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespdeffun(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespdeffun(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespdeffunrecContext extends ModelresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunRecContext cmddefineFunRec() {
      return getRuleContext(CmddefineFunRecContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public RespdeffunrecContext(ModelresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespdeffunrec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespdeffunrec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespdeffunrec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespdeffunsrecContext extends ModelresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public CmddefineFunsRecContext cmddefineFunsRec() {
      return getRuleContext(CmddefineFunsRecContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public RespdeffunsrecContext(ModelresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespdeffunsrec(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespdeffunsrec(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespdeffunsrec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ModelresponseContext modelresponse() throws RecognitionException {
    ModelresponseContext local_ctx = new ModelresponseContext(_ctx, getState());
    enterRule(local_ctx, 158, RULEmodelresponse);
    try {
      setState(976);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 63, _ctx)) {
        case 1:
          local_ctx = new RespdeffunContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(964);
            match(ParOpen);
            setState(965);
            cmddefineFun();
            setState(966);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new RespdeffunrecContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(968);
            match(ParOpen);
            setState(969);
            cmddefineFunRec();
            setState(970);
            match(ParClose);
          }
          break;
        case 3:
          local_ctx = new RespdeffunsrecContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(972);
            match(ParOpen);
            setState(973);
            cmddefineFunsRec();
            setState(974);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InforesponseContext extends ParserRuleContext {
    public InforesponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEinforesponse;
    }

    public InforesponseContext() {}

    public void copyFrom(InforesponseContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoauthorsContext extends InforesponseContext {
    public TerminalNode PKAuthors() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAuthors, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public InfoauthorsContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterInfoauthors(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfoauthors(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoauthors(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoversionContext extends InforesponseContext {
    public TerminalNode PKVersion() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKVersion, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public InfoversionContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterInfoversion(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfoversion(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoversion(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoattrContext extends InforesponseContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public InfoattrContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterInfoattr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfoattr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoattr(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoerrorContext extends InforesponseContext {
    public TerminalNode PKErrorBehaviour() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKErrorBehaviour, 0);
    }

    public ErrorbehaviourContext errorbehaviour() {
      return getRuleContext(ErrorbehaviourContext.class, 0);
    }

    public InfoerrorContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterInfoerror(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfoerror(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoerror(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfoassertstackContext extends InforesponseContext {
    public TerminalNode PKAssertionStackLevels() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKAssertionStackLevels,
          0);
    }

    public NumeralContext numeral() {
      return getRuleContext(NumeralContext.class, 0);
    }

    public InfoassertstackContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterInfoassertstack(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitInfoassertstack(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoassertstack(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InforunknownContext extends InforesponseContext {
    public TerminalNode PKReasonUnknown() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKReasonUnknown, 0);
    }

    public ReasonunknownContext reasonunknown() {
      return getRuleContext(ReasonunknownContext.class, 0);
    }

    public InforunknownContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterInforunknown(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitInforunknown(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInforunknown(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class InfonameContext extends InforesponseContext {
    public TerminalNode PKName() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PKName, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public InfonameContext(InforesponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterInfoname(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitInfoname(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitInfoname(this);
      else return visitor.visitChildren(this);
    }
  }

  public final InforesponseContext inforesponse() throws RecognitionException {
    InforesponseContext local_ctx = new InforesponseContext(_ctx, getState());
    enterRule(local_ctx, 160, RULEinforesponse);
    try {
      setState(991);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 64, _ctx)) {
        case 1:
          local_ctx = new InfoassertstackContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(978);
            match(PKAssertionStackLevels);
            setState(979);
            numeral();
          }
          break;
        case 2:
          local_ctx = new InfoauthorsContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(980);
            match(PKAuthors);
            setState(981);
            string();
          }
          break;
        case 3:
          local_ctx = new InfoerrorContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(982);
            match(PKErrorBehaviour);
            setState(983);
            errorbehaviour();
          }
          break;
        case 4:
          local_ctx = new InfonameContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(984);
            match(PKName);
            setState(985);
            string();
          }
          break;
        case 5:
          local_ctx = new InforunknownContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(986);
            match(PKReasonUnknown);
            setState(987);
            reasonunknown();
          }
          break;
        case 6:
          local_ctx = new InfoversionContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(988);
            match(PKVersion);
            setState(989);
            string();
          }
          break;
        case 7:
          local_ctx = new InfoattrContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(990);
            attribute();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ValuationpairContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public List<TermContext> term() {
      return getRuleContexts(TermContext.class);
    }

    public TermContext term(int i) {
      return getRuleContext(TermContext.class, i);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public ValuationpairContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEvaluationpair;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterValuationpair(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitValuationpair(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitValuationpair(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ValuationpairContext valuationpair() throws RecognitionException {
    ValuationpairContext local_ctx = new ValuationpairContext(_ctx, getState());
    enterRule(local_ctx, 162, RULEvaluationpair);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(993);
        match(ParOpen);
        setState(994);
        term();
        setState(995);
        term();
        setState(996);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class TvaluationpairContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public BvalueContext bvalue() {
      return getRuleContext(BvalueContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public TvaluationpairContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEtvaluationpair;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterTvaluationpair(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitTvaluationpair(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitTvaluationpair(this);
      else return visitor.visitChildren(this);
    }
  }

  public final TvaluationpairContext tvaluationpair() throws RecognitionException {
    TvaluationpairContext local_ctx = new TvaluationpairContext(_ctx, getState());
    enterRule(local_ctx, 164, RULEtvaluationpair);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(998);
        match(ParOpen);
        setState(999);
        symbol();
        setState(1000);
        bvalue();
        setState(1001);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ChecksatresponseContext extends ParserRuleContext {
    public TerminalNode PSSat() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSSat, 0);
    }

    public TerminalNode PSUnsat() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnsat, 0);
    }

    public TerminalNode PSUnknown() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnknown, 0);
    }

    public ChecksatresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEchecksatresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterChecksatresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitChecksatresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitChecksatresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ChecksatresponseContext checksatresponse() throws RecognitionException {
    ChecksatresponseContext local_ctx = new ChecksatresponseContext(_ctx, getState());
    enterRule(local_ctx, 166, RULEchecksatresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1003);
        la = _input.LA(1);
        if (!((((la) & ~0x3f) == 0 && ((1L << la) & 5308416L) != 0))) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class EchoresponseContext extends ParserRuleContext {
    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public EchoresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEechoresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterEchoresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitEchoresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitEchoresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final EchoresponseContext echoresponse() throws RecognitionException {
    EchoresponseContext local_ctx = new EchoresponseContext(_ctx, getState());
    enterRule(local_ctx, 168, RULEechoresponse);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1005);
        string();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetassertionsresponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<TermContext> term() {
      return getRuleContexts(TermContext.class);
    }

    public TermContext term(int i) {
      return getRuleContext(TermContext.class, i);
    }

    public GetassertionsresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetassertionsresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetassertionsresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetassertionsresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetassertionsresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetassertionsresponseContext getassertionsresponse() throws RecognitionException {
    GetassertionsresponseContext local_ctx = new GetassertionsresponseContext(_ctx, getState());
    enterRule(local_ctx, 170, RULEgetassertionsresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1007);
        match(ParOpen);
        setState(1011);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388580L) != 0)
            || ((((la - 66)) & ~0x3f) == 0 && ((1L << (la - 66)) & 144115188075864079L) != 0)) {
          {
            {
              setState(1008);
              term();
            }
          }
          setState(1013);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(1014);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetassignmentresponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<TvaluationpairContext> tvaluationpair() {
      return getRuleContexts(TvaluationpairContext.class);
    }

    public TvaluationpairContext tvaluationpair(int i) {
      return getRuleContext(TvaluationpairContext.class, i);
    }

    public GetassignmentresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetassignmentresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetassignmentresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetassignmentresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetassignmentresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetassignmentresponseContext getassignmentresponse() throws RecognitionException {
    GetassignmentresponseContext local_ctx = new GetassignmentresponseContext(_ctx, getState());
    enterRule(local_ctx, 172, RULEgetassignmentresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1016);
        match(ParOpen);
        setState(1020);
        _errHandler.sync(this);
        la = _input.LA(1);
        while (la == ParOpen) {
          {
            {
              setState(1017);
              tvaluationpair();
            }
          }
          setState(1022);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(1023);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetinforesponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<InforesponseContext> inforesponse() {
      return getRuleContexts(InforesponseContext.class);
    }

    public InforesponseContext inforesponse(int i) {
      return getRuleContext(InforesponseContext.class, i);
    }

    public GetinforesponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetinforesponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetinforesponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetinforesponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetinforesponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetinforesponseContext getinforesponse() throws RecognitionException {
    GetinforesponseContext local_ctx = new GetinforesponseContext(_ctx, getState());
    enterRule(local_ctx, 174, RULEgetinforesponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1025);
        match(ParOpen);
        setState(1027);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(1026);
              inforesponse();
            }
          }
          setState(1029);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (((((la - 80)) & ~0x3f) == 0 && ((1L << (la - 80)) & 4398046511103L) != 0));
        setState(1031);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetmodelresponseContext extends ParserRuleContext {
    public GetmodelresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetmodelresponse;
    }

    public GetmodelresponseContext() {}

    public void copyFrom(GetmodelresponseContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ModelrespContext extends GetmodelresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<ModelresponseContext> modelresponse() {
      return getRuleContexts(ModelresponseContext.class);
    }

    public ModelresponseContext modelresponse(int i) {
      return getRuleContext(ModelresponseContext.class, i);
    }

    public ModelrespContext(GetmodelresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterModelresp(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitModelresp(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitModelresp(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RsmodelContext extends GetmodelresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode RSModel() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.RSModel, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<ModelresponseContext> modelresponse() {
      return getRuleContexts(ModelresponseContext.class);
    }

    public ModelresponseContext modelresponse(int i) {
      return getRuleContext(ModelresponseContext.class, i);
    }

    public RsmodelContext(GetmodelresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRsmodel(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRsmodel(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRsmodel(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetmodelresponseContext getmodelresponse() throws RecognitionException {
    GetmodelresponseContext local_ctx = new GetmodelresponseContext(_ctx, getState());
    enterRule(local_ctx, 176, RULEgetmodelresponse);
    int la;
    try {
      setState(1050);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 70, _ctx)) {
        case 1:
          local_ctx = new RsmodelContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(1033);
            match(ParOpen);
            setState(1034);
            match(RSModel);
            setState(1038);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (la == ParOpen) {
              {
                {
                  setState(1035);
                  modelresponse();
                }
              }
              setState(1040);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(1041);
            match(ParClose);
          }
          break;
        case 2:
          local_ctx = new ModelrespContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(1042);
            match(ParOpen);
            setState(1046);
            _errHandler.sync(this);
            la = _input.LA(1);
            while (la == ParOpen) {
              {
                {
                  setState(1043);
                  modelresponse();
                }
              }
              setState(1048);
              _errHandler.sync(this);
              la = _input.LA(1);
            }
            setState(1049);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetoptionresponseContext extends ParserRuleContext {
    public AttributevalueContext attributevalue() {
      return getRuleContext(AttributevalueContext.class, 0);
    }

    public GetoptionresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetoptionresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetoptionresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetoptionresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetoptionresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetoptionresponseContext getoptionresponse() throws RecognitionException {
    GetoptionresponseContext local_ctx = new GetoptionresponseContext(_ctx, getState());
    enterRule(local_ctx, 178, RULEgetoptionresponse);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1052);
        attributevalue();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetproofresponseContext extends ParserRuleContext {
    public SexprContext sexpr() {
      return getRuleContext(SexprContext.class, 0);
    }

    public GetproofresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetproofresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetproofresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetproofresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetproofresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetproofresponseContext getproofresponse() throws RecognitionException {
    GetproofresponseContext local_ctx = new GetproofresponseContext(_ctx, getState());
    enterRule(local_ctx, 180, RULEgetproofresponse);
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1054);
        sexpr();
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetunsatassumpresponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public GetunsatassumpresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetunsatassumpresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetunsatassumpresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetunsatassumpresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetunsatassumpresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetunsatassumpresponseContext getunsatassumpresponse() throws RecognitionException {
    GetunsatassumpresponseContext local_ctx = new GetunsatassumpresponseContext(_ctx, getState());
    enterRule(local_ctx, 182, RULEgetunsatassumpresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1056);
        match(ParOpen);
        setState(1060);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0) || la == UndefinedSymbol) {
          {
            {
              setState(1057);
              symbol();
            }
          }
          setState(1062);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(1063);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetunsatcoreresponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<SymbolContext> symbol() {
      return getRuleContexts(SymbolContext.class);
    }

    public SymbolContext symbol(int i) {
      return getRuleContext(SymbolContext.class, i);
    }

    public GetunsatcoreresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetunsatcoreresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetunsatcoreresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetunsatcoreresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetunsatcoreresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetunsatcoreresponseContext getunsatcoreresponse() throws RecognitionException {
    GetunsatcoreresponseContext local_ctx = new GetunsatcoreresponseContext(_ctx, getState());
    enterRule(local_ctx, 184, RULEgetunsatcoreresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1065);
        match(ParOpen);
        setState(1069);
        _errHandler.sync(this);
        la = _input.LA(1);
        while ((((la) & ~0x3f) == 0 && ((1L << la) & 8388544L) != 0) || la == UndefinedSymbol) {
          {
            {
              setState(1066);
              symbol();
            }
          }
          setState(1071);
          _errHandler.sync(this);
          la = _input.LA(1);
        }
        setState(1072);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetvalueresponseContext extends ParserRuleContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public List<ValuationpairContext> valuationpair() {
      return getRuleContexts(ValuationpairContext.class);
    }

    public ValuationpairContext valuationpair(int i) {
      return getRuleContext(ValuationpairContext.class, i);
    }

    public GetvalueresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgetvalueresponse;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterGetvalueresponse(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitGetvalueresponse(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitGetvalueresponse(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetvalueresponseContext getvalueresponse() throws RecognitionException {
    GetvalueresponseContext local_ctx = new GetvalueresponseContext(_ctx, getState());
    enterRule(local_ctx, 186, RULEgetvalueresponse);
    int la;
    try {
      enterOuterAlt(local_ctx, 1);
      {
        setState(1074);
        match(ParOpen);
        setState(1076);
        _errHandler.sync(this);
        la = _input.LA(1);
        do {
          {
            {
              setState(1075);
              valuationpair();
            }
          }
          setState(1078);
          _errHandler.sync(this);
          la = _input.LA(1);
        } while (la == ParOpen);
        setState(1080);
        match(ParClose);
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SpecificsuccessresponseContext extends ParserRuleContext {
    public SpecificsuccessresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEspecificsuccessresponse;
    }

    public SpecificsuccessresponseContext() {}

    public void copyFrom(SpecificsuccessresponseContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespunsatcoreContext extends SpecificsuccessresponseContext {
    public GetunsatcoreresponseContext getunsatcoreresponse() {
      return getRuleContext(GetunsatcoreresponseContext.class, 0);
    }

    public RespunsatcoreContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespunsatcore(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespunsatcore(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespunsatcore(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespechoContext extends SpecificsuccessresponseContext {
    public EchoresponseContext echoresponse() {
      return getRuleContext(EchoresponseContext.class, 0);
    }

    public RespechoContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRespecho(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespecho(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespecho(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespgetassertContext extends SpecificsuccessresponseContext {
    public GetassertionsresponseContext getassertionsresponse() {
      return getRuleContext(GetassertionsresponseContext.class, 0);
    }

    public RespgetassertContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespgetassert(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespgetassert(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespgetassert(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespproofContext extends SpecificsuccessresponseContext {
    public GetproofresponseContext getproofresponse() {
      return getRuleContext(GetproofresponseContext.class, 0);
    }

    public RespproofContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRespproof(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespproof(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespproof(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespgetmodelContext extends SpecificsuccessresponseContext {
    public GetmodelresponseContext getmodelresponse() {
      return getRuleContext(GetmodelresponseContext.class, 0);
    }

    public RespgetmodelContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespgetmodel(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespgetmodel(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespgetmodel(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespchecksatContext extends SpecificsuccessresponseContext {
    public ChecksatresponseContext checksatresponse() {
      return getRuleContext(ChecksatresponseContext.class, 0);
    }

    public RespchecksatContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespchecksat(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespchecksat(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespchecksat(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespgetinfoContext extends SpecificsuccessresponseContext {
    public GetinforesponseContext getinforesponse() {
      return getRuleContext(GetinforesponseContext.class, 0);
    }

    public RespgetinfoContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespgetinfo(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespgetinfo(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespgetinfo(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespoptionContext extends SpecificsuccessresponseContext {
    public GetoptionresponseContext getoptionresponse() {
      return getRuleContext(GetoptionresponseContext.class, 0);
    }

    public RespoptionContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRespoption(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespoption(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespoption(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespunsatassumeContext extends SpecificsuccessresponseContext {
    public GetunsatassumpresponseContext getunsatassumpresponse() {
      return getRuleContext(GetunsatassumpresponseContext.class, 0);
    }

    public RespunsatassumeContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespunsatassume(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespunsatassume(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespunsatassume(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespvalueContext extends SpecificsuccessresponseContext {
    public GetvalueresponseContext getvalueresponse() {
      return getRuleContext(GetvalueresponseContext.class, 0);
    }

    public RespvalueContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterRespvalue(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespvalue(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespvalue(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespgettassignContext extends SpecificsuccessresponseContext {
    public GetassignmentresponseContext getassignmentresponse() {
      return getRuleContext(GetassignmentresponseContext.class, 0);
    }

    public RespgettassignContext(SpecificsuccessresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespgettassign(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespgettassign(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespgettassign(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SpecificsuccessresponseContext specificsuccessresponse()
      throws RecognitionException {
    SpecificsuccessresponseContext local_ctx = new SpecificsuccessresponseContext(_ctx, getState());
    enterRule(local_ctx, 188, RULEspecificsuccessresponse);
    try {
      setState(1093);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 74, _ctx)) {
        case 1:
          local_ctx = new RespchecksatContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(1082);
            checksatresponse();
          }
          break;
        case 2:
          local_ctx = new RespechoContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(1083);
            echoresponse();
          }
          break;
        case 3:
          local_ctx = new RespgetassertContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(1084);
            getassertionsresponse();
          }
          break;
        case 4:
          local_ctx = new RespgettassignContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(1085);
            getassignmentresponse();
          }
          break;
        case 5:
          local_ctx = new RespgetinfoContext(local_ctx);
          enterOuterAlt(local_ctx, 5);
          {
            setState(1086);
            getinforesponse();
          }
          break;
        case 6:
          local_ctx = new RespgetmodelContext(local_ctx);
          enterOuterAlt(local_ctx, 6);
          {
            setState(1087);
            getmodelresponse();
          }
          break;
        case 7:
          local_ctx = new RespoptionContext(local_ctx);
          enterOuterAlt(local_ctx, 7);
          {
            setState(1088);
            getoptionresponse();
          }
          break;
        case 8:
          local_ctx = new RespproofContext(local_ctx);
          enterOuterAlt(local_ctx, 8);
          {
            setState(1089);
            getproofresponse();
          }
          break;
        case 9:
          local_ctx = new RespunsatassumeContext(local_ctx);
          enterOuterAlt(local_ctx, 9);
          {
            setState(1090);
            getunsatassumpresponse();
          }
          break;
        case 10:
          local_ctx = new RespunsatcoreContext(local_ctx);
          enterOuterAlt(local_ctx, 10);
          {
            setState(1091);
            getunsatcoreresponse();
          }
          break;
        case 11:
          local_ctx = new RespvalueContext(local_ctx);
          enterOuterAlt(local_ctx, 11);
          {
            setState(1092);
            getvalueresponse();
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GeneralresponseContext extends ParserRuleContext {
    public GeneralresponseContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULEgeneralresponse;
    }

    public GeneralresponseContext() {}

    public void copyFrom(GeneralresponseContext _ctx) {
      super.copyFrom(_ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespunsupportedContext extends GeneralresponseContext {
    public TerminalNode PSUnsupported() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSUnsupported, 0);
    }

    public RespunsupportedContext(GeneralresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespunsupported(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespunsupported(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespunsupported(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespsuccessContext extends GeneralresponseContext {
    public TerminalNode PSSuccess() {
      return getToken(
          org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSSuccess, 0);
    }

    public RespsuccessContext(GeneralresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespsuccess(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitRespsuccess(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespsuccess(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RespspecsuccesssContext extends GeneralresponseContext {
    public SpecificsuccessresponseContext specificsuccessresponse() {
      return getRuleContext(SpecificsuccessresponseContext.class, 0);
    }

    public RespspecsuccesssContext(GeneralresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).enterRespspecsuccesss(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener)
        ((Smtlibv2Listener) listener).exitRespspecsuccesss(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitRespspecsuccesss(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResperrorContext extends GeneralresponseContext {
    public TerminalNode ParOpen() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParOpen, 0);
    }

    public TerminalNode PSError() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.PSError, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public TerminalNode ParClose() {
      return getToken(org.sosy_lab.java_smt.basicimpl.parserInterpreter.Smtlibv2Parser.ParClose, 0);
    }

    public ResperrorContext(GeneralresponseContext _ctx) {
      copyFrom(_ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).enterResperror(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof Smtlibv2Listener) ((Smtlibv2Listener) listener).exitResperror(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof Smtlibv2Visitor)
        return ((Smtlibv2Visitor<? extends T>) visitor).visitResperror(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GeneralresponseContext generalresponse() throws RecognitionException {
    GeneralresponseContext local_ctx = new GeneralresponseContext(_ctx, getState());
    enterRule(local_ctx, 190, RULEgeneralresponse);
    try {
      setState(1103);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 75, _ctx)) {
        case 1:
          local_ctx = new RespsuccessContext(local_ctx);
          enterOuterAlt(local_ctx, 1);
          {
            setState(1095);
            match(PSSuccess);
          }
          break;
        case 2:
          local_ctx = new RespspecsuccesssContext(local_ctx);
          enterOuterAlt(local_ctx, 2);
          {
            setState(1096);
            specificsuccessresponse();
          }
          break;
        case 3:
          local_ctx = new RespunsupportedContext(local_ctx);
          enterOuterAlt(local_ctx, 3);
          {
            setState(1097);
            match(PSUnsupported);
          }
          break;
        case 4:
          local_ctx = new ResperrorContext(local_ctx);
          enterOuterAlt(local_ctx, 4);
          {
            setState(1098);
            match(ParOpen);
            setState(1099);
            match(PSError);
            setState(1100);
            string();
            setState(1101);
            match(ParClose);
          }
          break;
      }
    } catch (RecognitionException re) {
      local_ctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return local_ctx;
  }

  public static final String serializedATN =
      "\u0004\u0001|\u0452\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"
          + "\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"
          + "\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"
          + "\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"
          + "\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"
          + "\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"
          + "\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002\u0015\u0007\u0015"
          + "\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017\u0002\u0018\u0007\u0018"
          + "\u0002\u0019\u0007\u0019\u0002\u001a\u0007\u001a\u0002\u001b\u0007\u001b"
          + "\u0002\u001c\u0007\u001c\u0002\u001d\u0007\u001d\u0002\u001e\u0007\u001e"
          + "\u0002\u001f\u0007\u001f\u0002 \u0007 \u0002!\u0007!\u0002\"\u0007\"\u0002"
          + "#\u0007#\u0002$\u0007$\u0002%\u0007%\u0002&\u0007&\u0002\'\u0007\'\u0002"
          + "(\u0007(\u0002)\u0007)\u0002*\u0007*\u0002+\u0007+\u0002,\u0007,\u0002"
          + "-\u0007-\u0002.\u0007.\u0002/\u0007/\u00020\u00070\u00021\u00071\u0002"
          + "2\u00072\u00023\u00073\u00024\u00074\u00025\u00075\u00026\u00076\u0002"
          + "7\u00077\u00028\u00078\u00029\u00079\u0002:\u0007:\u0002;\u0007;\u0002"
          + "<\u0007<\u0002=\u0007=\u0002>\u0007>\u0002?\u0007?\u0002@\u0007@\u0002"
          + "A\u0007A\u0002B\u0007B\u0002C\u0007C\u0002D\u0007D\u0002E\u0007E\u0002"
          + "F\u0007F\u0002G\u0007G\u0002H\u0007H\u0002I\u0007I\u0002J\u0007J\u0002"
          + "K\u0007K\u0002L\u0007L\u0002M\u0007M\u0002N\u0007N\u0002O\u0007O\u0002"
          + "P\u0007P\u0002Q\u0007Q\u0002R\u0007R\u0002S\u0007S\u0002T\u0007T\u0002"
          + "U\u0007U\u0002V\u0007V\u0002W\u0007W\u0002X\u0007X\u0002Y\u0007Y\u0002"
          + "Z\u0007Z\u0002[\u0007[\u0002\\\u0007\\\u0002]\u0007]\u0002^\u0007^\u0002"
          + "\u0007\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001"
          + "\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001"
          + "\u0000\u0003\u0000\u00cd\b\u0000\u0001\u0001\u0001\u0001\u0001\u0002\u0001"
          + "\u0002\u0003\u0002\u00d3\b\u0002\u0001\u0003\u0001\u0003\u0001\u0004\u0001"
          + "\u0004\u0001\u0005\u0001\u0005\u0001\u0006\u0001\u0006\u0003\u0006\u00dd"
          + "\b\u0006\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001\t\u0001\t\u0001"
          + "\n\u0001\n\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001\r\u0001\r\u0001"
          + "\r\u0003\r\u00ee\b\r\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001"
          + "\u000e\u0001\u000e\u0003\u000e\u00f6\b\u000e\u0001\u000f\u0001\u000f\u0001"
          + "\u000f\u0001\u000f\u0001\u000f\u0005\u000f\u00fd\b\u000f\n\u000f\f\u000f"
          + "\u0100\t\u000f\u0001\u000f\u0003\u000f\u0103\b\u000f\u0001\u0010\u0001"
          + "\u0010\u0003\u0010\u0107\b\u0010\u0001\u0011\u0001\u0011\u0001\u0011\u0001"
          + "\u0011\u0001\u0011\u0004\u0011\u010e\b\u0011\u000b\u0011\f\u0011\u010f"
          + "\u0001\u0011\u0001\u0011\u0003\u0011\u0114\b\u0011\u0001\u0012\u0001\u0012"
          + "\u0001\u0012\u0001\u0012\u0005\u0012\u011a\b\u0012\n\u0012\f\u0012\u011d"
          + "\t\u0012\u0001\u0012\u0003\u0012\u0120\b\u0012\u0001\u0013\u0001\u0013"
          + "\u0001\u0013\u0001\u0013\u0003\u0013\u0126\b\u0013\u0001\u0014\u0001\u0014"
          + "\u0001\u0014\u0001\u0014\u0004\u0014\u012c\b\u0014\u000b\u0014\f\u0014"
          + "\u012d\u0001\u0014\u0001\u0014\u0003\u0014\u0132\b\u0014\u0001\u0015\u0001"
          + "\u0015\u0001\u0015\u0001\u0015\u0001\u0015\u0001\u0015\u0001\u0015\u0003"
          + "\u0015\u013b\b\u0015\u0001\u0016\u0001\u0016\u0001\u0016\u0001\u0016\u0001"
          + "\u0016\u0001\u0017\u0001\u0017\u0001\u0017\u0001\u0017\u0001\u0017\u0001"
          + "\u0018\u0001\u0018\u0001\u0018\u0001\u0018\u0004\u0018\u014b\b\u0018\u000b"
          + "\u0018\f\u0018\u014c\u0001\u0018\u0001\u0018\u0003\u0018\u0151\b\u0018"
          + "\u0001\u0019\u0001\u0019\u0001\u0019\u0001\u0019\u0001\u0019\u0001\u001a"
          + "\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0004\u001a\u015d\b\u001a"
          + "\u000b\u001a\f\u001a\u015e\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a"
          + "\u0001\u001a\u0001\u001a\u0004\u001a\u0167\b\u001a\u000b\u001a\f\u001a"
          + "\u0168\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001"
          + "\u001a\u0001\u001a\u0001\u001a\u0004\u001a\u0173\b\u001a\u000b\u001a\f"
          + "\u001a\u0174\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a"
          + "\u0001\u001a\u0001\u001a\u0001\u001a\u0004\u001a\u017f\b\u001a\u000b\u001a"
          + "\f\u001a\u0180\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a"
          + "\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0004\u001a\u018c\b\u001a"
          + "\u000b\u001a\f\u001a\u018d\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a"
          + "\u0001\u001a\u0001\u001a\u0001\u001a\u0004\u001a\u0197\b\u001a\u000b\u001a"
          + "\f\u001a\u0198\u0001\u001a\u0001\u001a\u0003\u001a\u019d\b\u001a\u0001"
          + "\u001b\u0001\u001b\u0001\u001b\u0001\u001b\u0005\u001b\u01a3\b\u001b\n"
          + "\u001b\f\u001b\u01a6\t\u001b\u0001\u001b\u0001\u001b\u0001\u001c\u0001"
          + "\u001c\u0001\u001d\u0001\u001d\u0001\u001d\u0001\u001d\u0005\u001d\u01b0"
          + "\b\u001d\n\u001d\f\u001d\u01b3\t\u001d\u0001\u001d\u0001\u001d\u0001\u001d"
          + "\u0001\u001d\u0001\u001d\u0001\u001d\u0005\u001d\u01bb\b\u001d\n\u001d"
          + "\f\u001d\u01be\t\u001d\u0001\u001d\u0001\u001d\u0001\u001d\u0001\u001d"
          + "\u0001\u001d\u0004\u001d\u01c5\b\u001d\u000b\u001d\f\u001d\u01c6\u0001"
          + "\u001d\u0005\u001d\u01ca\b\u001d\n\u001d\f\u001d\u01cd\t\u001d\u0001\u001d"
          + "\u0001\u001d\u0003\u001d\u01d1\b\u001d\u0001\u001e\u0001\u001e\u0001\u001e"
          + "\u0001\u001e\u0001\u001e\u0004\u001e\u01d8\b\u001e\u000b\u001e\f\u001e"
          + "\u01d9\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0004\u001e\u01e0"
          + "\b\u001e\u000b\u001e\f\u001e\u01e1\u0001\u001e\u0005\u001e\u01e5\b\u001e"
          + "\n\u001e\f\u001e\u01e8\t\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0003"
          + "\u001e\u01ed\b\u001e\u0001\u001f\u0001\u001f\u0001\u001f\u0004\u001f\u01f2"
          + "\b\u001f\u000b\u001f\f\u001f\u01f3\u0001\u001f\u0001\u001f\u0001\u001f"
          + "\u0001\u001f\u0001\u001f\u0004\u001f\u01fb\b\u001f\u000b\u001f\f\u001f"
          + "\u01fc\u0001\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0001"
          + "\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0001"
          + "\u001f\u0001\u001f\u0003\u001f\u020c\b\u001f\u0001 \u0001 \u0001 \u0001"
          + " \u0004 \u0212\b \u000b \f \u0213\u0001 \u0001 \u0001!\u0001!\u0001!\u0004"
          + "!\u021b\b!\u000b!\f!\u021c\u0001!\u0001!\u0001!\u0001!\u0001!\u0001!\u0001"
          + "!\u0001!\u0001!\u0001!\u0001!\u0003!\u022a\b!\u0001\"\u0001\"\u0001\""
          + "\u0001\"\u0004\"\u0230\b\"\u000b\"\f\"\u0231\u0001\"\u0001\"\u0001#\u0001"
          + "#\u0001#\u0001#\u0001#\u0001$\u0001$\u0001$\u0001$\u0001$\u0001%\u0001"
          + "%\u0001%\u0005%\u0243\b%\n%\f%\u0246\t%\u0001%\u0001%\u0001&\u0001&\u0004"
          + "&\u024c\b&\u000b&\f&\u024d\u0001&\u0001&\u0001&\u0001&\u0001&\u0001&\u0004"
          + "&\u0256\b&\u000b&\f&\u0257\u0001&\u0001&\u0001&\u0004&\u025d\b&\u000b"
          + "&\f&\u025e\u0001&\u0001&\u0001&\u0003&\u0264\b&\u0001\'\u0001\'\u0001"
          + "\'\u0001\'\u0005\'\u026a\b\'\n\'\f\'\u026d\t\'\u0001\'\u0001\'\u0001\'"
          + "\u0001\'\u0001(\u0001(\u0001(\u0005(\u0276\b(\n(\f(\u0279\t(\u0001(\u0001"
          + "(\u0001(\u0001(\u0001)\u0001)\u0001)\u0001)\u0001)\u0001)\u0003)\u0285"
          + "\b)\u0001*\u0005*\u0288\b*\n*\f*\u028b\t*\u0001+\u0001+\u0001+\u0001,"
          + "\u0001,\u0001-\u0001-\u0001-\u0005-\u0295\b-\n-\f-\u0298\t-\u0001-\u0001"
          + "-\u0001.\u0001.\u0001.\u0001.\u0001/\u0001/\u0001/\u0001/\u00010\u0001"
          + "0\u00010\u00040\u02a7\b0\u000b0\f0\u02a8\u00010\u00010\u00010\u00040\u02ae"
          + "\b0\u000b0\f0\u02af\u00010\u00010\u00011\u00011\u00011\u00011\u00051\u02b8"
          + "\b1\n1\f1\u02bb\t1\u00011\u00011\u00011\u00012\u00012\u00012\u00012\u0001"
          + "3\u00013\u00013\u00014\u00014\u00014\u00015\u00015\u00015\u00045\u02cd"
          + "\b5\u000b5\f5\u02ce\u00015\u00015\u00015\u00045\u02d4\b5\u000b5\f5\u02d5"
          + "\u00015\u00015\u00016\u00016\u00016\u00016\u00056\u02de\b6\n6\f6\u02e1"
          + "\t6\u00016\u00016\u00016\u00017\u00017\u00017\u00018\u00018\u00019\u0001"
          + "9\u0001:\u0001:\u0001;\u0001;\u0001;\u0001<\u0001<\u0001=\u0001=\u0001"
          + "=\u0001>\u0001>\u0001?\u0001?\u0001@\u0001@\u0001A\u0001A\u0001A\u0004"
          + "A\u0300\bA\u000bA\fA\u0301\u0001A\u0001A\u0001B\u0001B\u0001B\u0001C\u0001"
          + "C\u0001C\u0001D\u0001D\u0001E\u0001E\u0001F\u0001F\u0001F\u0001G\u0001"
          + "G\u0001G\u0001H\u0001H\u0001H\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001I\u0001"
          + "I\u0001I\u0001I\u0001I\u0001I\u0003I\u0391\bI\u0001J\u0001J\u0001K\u0001"
          + "K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001"
          + "K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001"
          + "K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0001K\u0003K\u03b2\bK\u0001"
          + "L\u0001L\u0001L\u0001L\u0001L\u0001L\u0001L\u0001L\u0003L\u03bc\bL\u0001"
          + "M\u0001M\u0001N\u0001N\u0001N\u0003N\u03c3\bN\u0001O\u0001O\u0001O\u0001"
          + "O\u0001O\u0001O\u0001O\u0001O\u0001O\u0001O\u0001O\u0001O\u0003O\u03d1"
          + "\bO\u0001P\u0001P\u0001P\u0001P\u0001P\u0001P\u0001P\u0001P\u0001P\u0001"
          + "P\u0001P\u0001P\u0001P\u0003P\u03e0\bP\u0001Q\u0001Q\u0001Q\u0001Q\u0001"
          + "Q\u0001R\u0001R\u0001R\u0001R\u0001R\u0001S\u0001S\u0001T\u0001T\u0001"
          + "U\u0001U\u0005U\u03f2\bU\nU\fU\u03f5\tU\u0001U\u0001U\u0001V\u0001V\u0005"
          + "V\u03fb\bV\nV\fV\u03fe\tV\u0001V\u0001V\u0001W\u0001W\u0004W\u0404\bW"
          + "\u000bW\fW\u0405\u0001W\u0001W\u0001X\u0001X\u0001X\u0005X\u040d\bX\n"
          + "X\fX\u0410\tX\u0001X\u0001X\u0001X\u0005X\u0415\bX\nX\fX\u0418\tX\u0001"
          + "X\u0003X\u041b\bX\u0001Y\u0001Y\u0001Z\u0001Z\u0001[\u0001[\u0005[\u0423"
          + "\b[\n[\f[\u0426\t[\u0001[\u0001[\u0001\\\u0001\\\u0005\\\u042c\b\\\n\\"
          + "\f\\\u042f\t\\\u0001\\\u0001\\\u0001]\u0001]\u0004]\u0435\b]\u000b]\f"
          + "]\u0436\u0001]\u0001]\u0001^\u0001^\u0001^\u0001^\u0001^\u0001^\u0001"
          + "^\u0001^\u0001^\u0001^\u0001^\u0003^\u0446\b^\u0001\u0001\u0001\u0001"
          + "\u0001\u0001\u0001\u0001\u0003\u0450\b\u0001\u0000\u0000`\u0000"
          + "\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0018\u001a\u001c"
          + "\u001e \"$&(*,.02468:<>@BDFHJLNPRTVXZ\\^`bdfhjlnprtvxz|~\u0080\u0082\u0084"
          + "\u0086\u0088\u008a\u008c\u008e\u0090\u0092\u0094\u0096\u0098\u009a\u009c"
          + "\u009e\u00a0\u00a2\u00a4\u00a6\u00a8\u00aa\u00ac\u00ae\u00b0\u00b2\u00b4"
          + "\u00b6\u00b8\u00ba\u00bc\u00be\u0000\u0007\u0002\u00005Azz\u0001\u0000"
          + "\u0007\u0016\u0001\u0000Qy\u0003\u000099??AA\u0002\u0000\u000b\u000b\u0013"
          + "\u0013\u0002\u0000\t\t\f\f\u0003\u0000\u0010\u0010\u0014\u0014\u0016\u0016"
          + "\u0498\u0000\u00cc\u0001\u0000\u0000\u0000\u0002\u00ce\u0001\u0000\u0000"
          + "\u0000\u0004\u00d2\u0001\u0000\u0000\u0000\u0006\u00d4\u0001\u0000\u0000"
          + "\u0000\b\u00d6\u0001\u0000\u0000\u0000\n\u00d8\u0001\u0000\u0000\u0000"
          + "\f\u00dc\u0001\u0000\u0000\u0000\u000e\u00de\u0001\u0000\u0000\u0000\u0010"
          + "\u00e0\u0001\u0000\u0000\u0000\u0012\u00e2\u0001\u0000\u0000\u0000\u0014"
          + "\u00e4\u0001\u0000\u0000\u0000\u0016\u00e6\u0001\u0000\u0000\u0000\u0018"
          + "\u00e8\u0001\u0000\u0000\u0000\u001a\u00ed\u0001\u0000\u0000\u0000\u001c"
          + "\u00f5\u0001\u0000\u0000\u0000\u001e\u0102\u0001\u0000\u0000\u0000 \u0106"
          + "\u0001\u0000\u0000\u0000\"\u0113\u0001\u0000\u0000\u0000$\u011f\u0001"
          + "\u0000\u0000\u0000&\u0125\u0001\u0000\u0000\u0000(\u0131\u0001\u0000\u0000"
          + "\u0000*\u013a\u0001\u0000\u0000\u0000,\u013c\u0001\u0000\u0000\u0000."
          + "\u0141\u0001\u0000\u0000\u00000\u0150\u0001\u0000\u0000\u00002\u0152\u0001"
          + "\u0000\u0000\u00004\u019c\u0001\u0000\u0000\u00006\u019e\u0001\u0000\u0000"
          + "\u00008\u01a9\u0001\u0000\u0000\u0000:\u01d0\u0001\u0000\u0000\u0000<"
          + "\u01ec\u0001\u0000\u0000\u0000>\u020b\u0001\u0000\u0000\u0000@\u020d\u0001"
          + "\u0000\u0000\u0000B\u0229\u0001\u0000\u0000\u0000D\u022b\u0001\u0000\u0000"
          + "\u0000F\u0235\u0001\u0000\u0000\u0000H\u023a\u0001\u0000\u0000\u0000J"
          + "\u023f\u0001\u0000\u0000\u0000L\u0263\u0001\u0000\u0000\u0000N\u0265\u0001"
          + "\u0000\u0000\u0000P\u0272\u0001\u0000\u0000\u0000R\u0284\u0001\u0000\u0000"
          + "\u0000T\u0289\u0001\u0000\u0000\u0000V\u028c\u0001\u0000\u0000\u0000X"
          + "\u028f\u0001\u0000\u0000\u0000Z\u0291\u0001\u0000\u0000\u0000\\\u029b"
          + "\u0001\u0000\u0000\u0000^\u029f\u0001\u0000\u0000\u0000`\u02a3\u0001\u0000"
          + "\u0000\u0000b\u02b3\u0001\u0000\u0000\u0000d\u02bf\u0001\u0000\u0000\u0000"
          + "f\u02c3\u0001\u0000\u0000\u0000h\u02c6\u0001\u0000\u0000\u0000j\u02c9"
          + "\u0001\u0000\u0000\u0000l\u02d9\u0001\u0000\u0000\u0000n\u02e5\u0001\u0000"
          + "\u0000\u0000p\u02e8\u0001\u0000\u0000\u0000r\u02ea\u0001\u0000\u0000\u0000"
          + "t\u02ec\u0001\u0000\u0000\u0000v\u02ee\u0001\u0000\u0000\u0000x\u02f1"
          + "\u0001\u0000\u0000\u0000z\u02f3\u0001\u0000\u0000\u0000|\u02f6\u0001\u0000"
          + "\u0000\u0000~\u02f8\u0001\u0000\u0000\u0000\u0080\u02fa\u0001\u0000\u0000"
          + "\u0000\u0082\u02fc\u0001\u0000\u0000\u0000\u0084\u0305\u0001\u0000\u0000"
          + "\u0000\u0086\u0308\u0001\u0000\u0000\u0000\u0088\u030b\u0001\u0000\u0000"
          + "\u0000\u008a\u030d\u0001\u0000\u0000\u0000\u008c\u030f\u0001\u0000\u0000"
          + "\u0000\u008e\u0312\u0001\u0000\u0000\u0000\u0090\u0315\u0001\u0000\u0000"
          + "\u0000\u0092\u0390\u0001\u0000\u0000\u0000\u0094\u0392\u0001\u0000\u0000"
          + "\u0000\u0096\u03b1\u0001\u0000\u0000\u0000\u0098\u03bb\u0001\u0000\u0000"
          + "\u0000\u009a\u03bd\u0001\u0000\u0000\u0000\u009c\u03c2\u0001\u0000\u0000"
          + "\u0000\u009e\u03d0\u0001\u0000\u0000\u0000\u00a0\u03df\u0001\u0000\u0000"
          + "\u0000\u00a2\u03e1\u0001\u0000\u0000\u0000\u00a4\u03e6\u0001\u0000\u0000"
          + "\u0000\u00a6\u03eb\u0001\u0000\u0000\u0000\u00a8\u03ed\u0001\u0000\u0000"
          + "\u0000\u00aa\u03ef\u0001\u0000\u0000\u0000\u00ac\u03f8\u0001\u0000\u0000"
          + "\u0000\u00ae\u0401\u0001\u0000\u0000\u0000\u00b0\u041a\u0001\u0000\u0000"
          + "\u0000\u00b2\u041c\u0001\u0000\u0000\u0000\u00b4\u041e\u0001\u0000\u0000"
          + "\u0000\u00b6\u0420\u0001\u0000\u0000\u0000\u00b8\u0429\u0001\u0000\u0000"
          + "\u0000\u00ba\u0432\u0001\u0000\u0000\u0000\u00bc\u0445\u0001\u0000\u0000"
          + "\u0000\u00be\u044f\u0001\u0000\u0000\u0000\u00c0\u00c1\u0003D\"\u0000"
          + "\u00c1\u00c2\u0005\u0000\u0000\u0001\u00c2\u00cd\u0001\u0000\u0000\u0000"
          + "\u00c3\u00c4\u0003@ \u0000\u00c4\u00c5\u0005\u0000\u0000\u0001\u00c5\u00cd"
          + "\u0001\u0000\u0000\u0000\u00c6\u00c7\u0003T*\u0000\u00c7\u00c8\u0005\u0000"
          + "\u0000\u0001\u00c8\u00cd\u0001\u0000\u0000\u0000\u00c9\u00ca\u0003\u00be"
          + "\u0000\u00ca\u00cb\u0005\u0000\u0000\u0001\u00cb\u00cd\u0001\u0000\u0000"
          + "\u0000\u00cc\u00c0\u0001\u0000\u0000\u0000\u00cc\u00c3\u0001\u0000\u0000"
          + "\u0000\u00cc\u00c6\u0001\u0000\u0000\u0000\u00cc\u00c9\u0001\u0000\u0000"
          + "\u0000\u00cd\u0001\u0001\u0000\u0000\u0000\u00ce\u00cf\u0007\u0000\u0000"
          + "\u0000\u00cf\u0003\u0001\u0000\u0000\u0000\u00d0\u00d3\u0003\b\u0004\u0000"
          + "\u00d1\u00d3\u0005{\u0000\u0000\u00d2\u00d0\u0001\u0000\u0000\u0000\u00d2"
          + "\u00d1\u0001\u0000\u0000\u0000\u00d3\u0005\u0001\u0000\u0000\u0000\u00d4"
          + "\u00d5\u0005\u0006\u0000\u0000\u00d5\u0007\u0001\u0000\u0000\u0000\u00d6"
          + "\u00d7\u0007\u0001\u0000\u0000\u00d7\t\u0001\u0000\u0000\u0000\u00d8\u00d9"
          + "\u0007\u0002\u0000\u0000\u00d9\u000b\u0001\u0000\u0000\u0000\u00da\u00dd"
          + "\u0003\u0004\u0002\u0000\u00db\u00dd\u0003\u0006\u0003\u0000\u00dc\u00da"
          + "\u0001\u0000\u0000\u0000\u00dc\u00db\u0001\u0000\u0000\u0000\u00dd\r\u0001"
          + "\u0000\u0000\u0000\u00de\u00df\u0005B\u0000\u0000\u00df\u000f\u0001\u0000"
          + "\u0000\u0000\u00e0\u00e1\u0005E\u0000\u0000\u00e1\u0011\u0001\u0000\u0000"
          + "\u0000\u00e2\u00e3\u0005D\u0000\u0000\u00e3\u0013\u0001\u0000\u0000\u0000"
          + "\u00e4\u00e5\u0005C\u0000\u0000\u00e5\u0015\u0001\u0000\u0000\u0000\u00e6"
          + "\u00e7\u0005\u0005\u0000\u0000\u00e7\u0017\u0001\u0000\u0000\u0000\u00e8"
          + "\u00e9\u0005O\u0000\u0000\u00e9\u0019\u0001\u0000\u0000\u0000\u00ea\u00ee"
          + "\u0003\n\u0005\u0000\u00eb\u00ec\u0005P\u0000\u0000\u00ec\u00ee\u0003"
          + "\u0004\u0002\u0000\u00ed\u00ea\u0001\u0000\u0000\u0000\u00ed\u00eb\u0001"
          + "\u0000\u0000\u0000\u00ee\u001b\u0001\u0000\u0000\u0000\u00ef\u00f6\u0003"
          + "\u000e\u0007\u0000\u00f0\u00f6\u0003\u0010\b\u0000\u00f1\u00f6\u0003\u0012"
          + "\t\u0000\u00f2\u00f6\u0003\u0014\n\u0000\u00f3\u00f6\u0003\u0016\u000b"
          + "\u0000\u00f4\u00f6\u0003\u0018\f\u0000\u00f5\u00ef\u0001\u0000\u0000\u0000"
          + "\u00f5\u00f0\u0001\u0000\u0000\u0000\u00f5\u00f1\u0001\u0000\u0000\u0000"
          + "\u00f5\u00f2\u0001\u0000\u0000\u0000\u00f5\u00f3\u0001\u0000\u0000\u0000"
          + "\u00f5\u00f4\u0001\u0000\u0000\u0000\u00f6\u001d\u0001\u0000\u0000\u0000"
          + "\u00f7\u0103\u0003\u001c\u000e\u0000\u00f8\u0103\u0003\f\u0006\u0000\u00f9"
          + "\u0103\u0003\u001a\r\u0000\u00fa\u00fe\u0005\u0002\u0000\u0000\u00fb\u00fd"
          + "\u0003\u001e\u000f\u0000\u00fc\u00fb\u0001\u0000\u0000\u0000\u00fd\u0100"
          + "\u0001\u0000\u0000\u0000\u00fe\u00fc\u0001\u0000\u0000\u0000\u00fe\u00ff"
          + "\u0001\u0000\u0000\u0000\u00ff\u0101\u0001\u0000\u0000\u0000\u0100\u00fe"
          + "\u0001\u0000\u0000\u0000\u0101\u0103\u0005\u0003\u0000\u0000\u0102\u00f7"
          + "\u0001\u0000\u0000\u0000\u0102\u00f8\u0001\u0000\u0000\u0000\u0102\u00f9"
          + "\u0001\u0000\u0000\u0000\u0102\u00fa\u0001\u0000\u0000\u0000\u0103\u001f"
          + "\u0001\u0000\u0000\u0000\u0104\u0107\u0003\u000e\u0007\u0000\u0105\u0107"
          + "\u0003\f\u0006\u0000\u0106\u0104\u0001\u0000\u0000\u0000\u0106\u0105\u0001"
          + "\u0000\u0000\u0000\u0107!\u0001\u0000\u0000\u0000\u0108\u0114\u0003\f"
          + "\u0006\u0000\u0109\u010a\u0005\u0002\u0000\u0000\u010a\u010b\u00056\u0000"
          + "\u0000\u010b\u010d\u0003\f\u0006\u0000\u010c\u010e\u0003 \u0010\u0000"
          + "\u010d\u010c\u0001\u0000\u0000\u0000\u010e\u010f\u0001\u0000\u0000\u0000"
          + "\u010f\u010d\u0001\u0000\u0000\u0000\u010f\u0110\u0001\u0000\u0000\u0000"
          + "\u0110\u0111\u0001\u0000\u0000\u0000\u0111\u0112\u0005\u0003\u0000\u0000"
          + "\u0112\u0114\u0001\u0000\u0000\u0000\u0113\u0108\u0001\u0000\u0000\u0000"
          + "\u0113\u0109\u0001\u0000\u0000\u0000\u0114#\u0001\u0000\u0000\u0000\u0115"
          + "\u0120\u0003\u001c\u000e\u0000\u0116\u0120\u0003\f\u0006\u0000\u0117\u011b"
          + "\u0005\u0002\u0000\u0000\u0118\u011a\u0003\u001e\u000f\u0000\u0119\u0118"
          + "\u0001\u0000\u0000\u0000\u011a\u011d\u0001\u0000\u0000\u0000\u011b\u0119"
          + "\u0001\u0000\u0000\u0000\u011b\u011c\u0001\u0000\u0000\u0000\u011c\u011e"
          + "\u0001\u0000\u0000\u0000\u011d\u011b\u0001\u0000\u0000\u0000\u011e\u0120"
          + "\u0005\u0003\u0000\u0000\u011f\u0115\u0001\u0000\u0000\u0000\u011f\u0116"
          + "\u0001\u0000\u0000\u0000\u011f\u0117\u0001\u0000\u0000\u0000\u0120%\u0001"
          + "\u0000\u0000\u0000\u0121\u0126\u0003\u001a\r\u0000\u0122\u0123\u0003\u001a"
          + "\r\u0000\u0123\u0124\u0003$\u0012\u0000\u0124\u0126\u0001\u0000\u0000"
          + "\u0000\u0125\u0121\u0001\u0000\u0000\u0000\u0125\u0122\u0001\u0000\u0000"
          + "\u0000\u0126\'\u0001\u0000\u0000\u0000\u0127\u0132\u0003\"\u0011\u0000"
          + "\u0128\u0129\u0005\u0002\u0000\u0000\u0129\u012b\u0003\"\u0011\u0000\u012a"
          + "\u012c\u0003(\u0014\u0000\u012b\u012a\u0001\u0000\u0000\u0000\u012c\u012d"
          + "\u0001\u0000\u0000\u0000\u012d\u012b\u0001\u0000\u0000\u0000\u012d\u012e"
          + "\u0001\u0000\u0000\u0000\u012e\u012f\u0001\u0000\u0000\u0000\u012f\u0130"
          + "\u0005\u0003\u0000\u0000\u0130\u0132\u0001\u0000\u0000\u0000\u0131\u0127"
          + "\u0001\u0000\u0000\u0000\u0131\u0128\u0001\u0000\u0000\u0000\u0132)\u0001"
          + "\u0000\u0000\u0000\u0133\u013b\u0003\"\u0011\u0000\u0134\u0135\u0005\u0002"
          + "\u0000\u0000\u0135\u0136\u00057\u0000\u0000\u0136\u0137\u0003\"\u0011"
          + "\u0000\u0137\u0138\u0003(\u0014\u0000\u0138\u0139\u0005\u0003\u0000\u0000"
          + "\u0139\u013b\u0001\u0000\u0000\u0000\u013a\u0133\u0001\u0000\u0000\u0000"
          + "\u013a\u0134\u0001\u0000\u0000\u0000\u013b+\u0001\u0000\u0000\u0000\u013c"
          + "\u013d\u0005\u0002\u0000\u0000\u013d\u013e\u0003\f\u0006\u0000\u013e\u013f"
          + "\u00034\u001a\u0000\u013f\u0140\u0005\u0003\u0000\u0000\u0140-\u0001\u0000"
          + "\u0000\u0000\u0141\u0142\u0005\u0002\u0000\u0000\u0142\u0143\u0003\f\u0006"
          + "\u0000\u0143\u0144\u0003(\u0014\u0000\u0144\u0145\u0005\u0003\u0000\u0000"
          + "\u0145/\u0001\u0000\u0000\u0000\u0146\u0151\u0003\f\u0006\u0000\u0147"
          + "\u0148\u0005\u0002\u0000\u0000\u0148\u014a\u0003\f\u0006\u0000\u0149\u014b"
          + "\u0003\f\u0006\u0000\u014a\u0149\u0001\u0000\u0000\u0000\u014b\u014c\u0001"
          + "\u0000\u0000\u0000\u014c\u014a\u0001\u0000\u0000\u0000\u014c\u014d\u0001"
          + "\u0000\u0000\u0000\u014d\u014e\u0001\u0000\u0000\u0000\u014e\u014f\u0005"
          + "\u0003\u0000\u0000\u014f\u0151\u0001\u0000\u0000\u0000\u0150\u0146\u0001"
          + "\u0000\u0000\u0000\u0150\u0147\u0001\u0000\u0000\u0000\u01511\u0001\u0000"
          + "\u0000\u0000\u0152\u0153\u0005\u0002\u0000\u0000\u0153\u0154\u00030\u0018"
          + "\u0000\u0154\u0155\u00034\u001a\u0000\u0155\u0156\u0005\u0003\u0000\u0000"
          + "\u01563\u0001\u0000\u0000\u0000\u0157\u019d\u0003\u001c\u000e\u0000\u0158"
          + "\u019d\u0003*\u0015\u0000\u0159\u015a\u0005\u0002\u0000\u0000\u015a\u015c"
          + "\u0003*\u0015\u0000\u015b\u015d\u00034\u001a\u0000\u015c\u015b\u0001\u0000"
          + "\u0000\u0000\u015d\u015e\u0001\u0000\u0000\u0000\u015e\u015c\u0001\u0000"
          + "\u0000\u0000\u015e\u015f\u0001\u0000\u0000\u0000\u015f\u0160\u0001\u0000"
          + "\u0000\u0000\u0160\u0161\u0005\u0003\u0000\u0000\u0161\u019d\u0001\u0000"
          + "\u0000\u0000\u0162\u0163\u0005\u0002\u0000\u0000\u0163\u0164\u0005=\u0000"
          + "\u0000\u0164\u0166\u0005\u0002\u0000\u0000\u0165\u0167\u0003,\u0016\u0000"
          + "\u0166\u0165\u0001\u0000\u0000\u0000\u0167\u0168\u0001\u0000\u0000\u0000"
          + "\u0168\u0166\u0001\u0000\u0000\u0000\u0168\u0169\u0001\u0000\u0000\u0000"
          + "\u0169\u016a\u0001\u0000\u0000\u0000\u016a\u016b\u0005\u0003\u0000\u0000"
          + "\u016b\u016c\u00034\u001a\u0000\u016c\u016d\u0005\u0003\u0000\u0000\u016d"
          + "\u019d\u0001\u0000\u0000\u0000\u016e\u016f\u0005\u0002\u0000\u0000\u016f"
          + "\u0170\u0005<\u0000\u0000\u0170\u0172\u0005\u0002\u0000\u0000\u0171\u0173"
          + "\u0003.\u0017\u0000\u0172\u0171\u0001\u0000\u0000\u0000\u0173\u0174\u0001"
          + "\u0000\u0000\u0000\u0174\u0172\u0001\u0000\u0000\u0000\u0174\u0175\u0001"
          + "\u0000\u0000\u0000\u0175\u0176\u0001\u0000\u0000\u0000\u0176\u0177\u0005"
          + "\u0003\u0000\u0000\u0177\u0178\u00034\u001a\u0000\u0178\u0179\u0005\u0003"
          + "\u0000\u0000\u0179\u019d\u0001\u0000\u0000\u0000\u017a\u017b\u0005\u0002"
          + "\u0000\u0000\u017b\u017c\u0005:\u0000\u0000\u017c\u017e\u0005\u0002\u0000"
          + "\u0000\u017d\u017f\u0003.\u0017\u0000\u017e\u017d\u0001\u0000\u0000\u0000"
          + "\u017f\u0180\u0001\u0000\u0000\u0000\u0180\u017e\u0001\u0000\u0000\u0000"
          + "\u0180\u0181\u0001\u0000\u0000\u0000\u0181\u0182\u0001\u0000\u0000\u0000"
          + "\u0182\u0183\u0005\u0003\u0000\u0000\u0183\u0184\u00034\u001a\u0000\u0184"
          + "\u0185\u0005\u0003\u0000\u0000\u0185\u019d\u0001\u0000\u0000\u0000\u0186"
          + "\u0187\u0005\u0002\u0000\u0000\u0187\u0188\u0005>\u0000\u0000\u0188\u0189"
          + "\u00034\u001a\u0000\u0189\u018b\u0005\u0002\u0000\u0000\u018a\u018c\u0003"
          + "2\u0019\u0000\u018b\u018a\u0001\u0000\u0000\u0000\u018c\u018d\u0001\u0000"
          + "\u0000\u0000\u018d\u018b\u0001\u0000\u0000\u0000\u018d\u018e\u0001\u0000"
          + "\u0000\u0000\u018e\u018f\u0001\u0000\u0000\u0000\u018f\u0190\u0005\u0003"
          + "\u0000\u0000\u0190\u0191\u0005\u0003\u0000\u0000\u0191\u019d\u0001\u0000"
          + "\u0000\u0000\u0192\u0193\u0005\u0002\u0000\u0000\u0193\u0194\u00055\u0000"
          + "\u0000\u0194\u0196\u00034\u001a\u0000\u0195\u0197\u0003&\u0013\u0000\u0196"
          + "\u0195\u0001\u0000\u0000\u0000\u0197\u0198\u0001\u0000\u0000\u0000\u0198"
          + "\u0196\u0001\u0000\u0000\u0000\u0198\u0199\u0001\u0000\u0000\u0000\u0199"
          + "\u019a\u0001\u0000\u0000\u0000\u019a\u019b\u0005\u0003\u0000\u0000\u019b"
          + "\u019d\u0001\u0000\u0000\u0000\u019c\u0157\u0001\u0000\u0000\u0000\u019c"
          + "\u0158\u0001\u0000\u0000\u0000\u019c\u0159\u0001\u0000\u0000\u0000\u019c"
          + "\u0162\u0001\u0000\u0000\u0000\u019c\u016e\u0001\u0000\u0000\u0000\u019c"
          + "\u017a\u0001\u0000\u0000\u0000\u019c\u0186\u0001\u0000\u0000\u0000\u019c"
          + "\u0192\u0001\u0000\u0000\u0000\u019d5\u0001\u0000\u0000\u0000\u019e\u019f"
          + "\u0005\u0002\u0000\u0000\u019f\u01a0\u0003\"\u0011\u0000\u01a0\u01a4\u0003"
          + "\u000e\u0007\u0000\u01a1\u01a3\u0003&\u0013\u0000\u01a2\u01a1\u0001\u0000"
          + "\u0000\u0000\u01a3\u01a6\u0001\u0000\u0000\u0000\u01a4\u01a2\u0001\u0000"
          + "\u0000\u0000\u01a4\u01a5\u0001\u0000\u0000\u0000\u01a5\u01a7\u0001\u0000"
          + "\u0000\u0000\u01a6\u01a4\u0001\u0000\u0000\u0000\u01a7\u01a8\u0005\u0003"
          + "\u0000\u0000\u01a87\u0001\u0000\u0000\u0000\u01a9\u01aa\u0007\u0003\u0000"
          + "\u0000\u01aa9\u0001\u0000\u0000\u0000\u01ab\u01ac\u0005\u0002\u0000\u0000"
          + "\u01ac\u01ad\u0003\u001c\u000e\u0000\u01ad\u01b1\u0003(\u0014\u0000\u01ae"
          + "\u01b0\u0003&\u0013\u0000\u01af\u01ae\u0001\u0000\u0000\u0000\u01b0\u01b3"
          + "\u0001\u0000\u0000\u0000\u01b1\u01af\u0001\u0000\u0000\u0000\u01b1\u01b2"
          + "\u0001\u0000\u0000\u0000\u01b2\u01b4\u0001\u0000\u0000\u0000\u01b3\u01b1"
          + "\u0001\u0000\u0000\u0000\u01b4\u01b5\u0005\u0003\u0000\u0000\u01b5\u01d1"
          + "\u0001\u0000\u0000\u0000\u01b6\u01b7\u0005\u0002\u0000\u0000\u01b7\u01b8"
          + "\u00038\u001c\u0000\u01b8\u01bc\u0003(\u0014\u0000\u01b9\u01bb\u0003&"
          + "\u0013\u0000\u01ba\u01b9\u0001\u0000\u0000\u0000\u01bb\u01be\u0001\u0000"
          + "\u0000\u0000\u01bc\u01ba\u0001\u0000\u0000\u0000\u01bc\u01bd\u0001\u0000"
          + "\u0000\u0000\u01bd\u01bf\u0001\u0000\u0000\u0000\u01be\u01bc\u0001\u0000"
          + "\u0000\u0000\u01bf\u01c0\u0005\u0003\u0000\u0000\u01c0\u01d1\u0001\u0000"
          + "\u0000\u0000\u01c1\u01c2\u0005\u0002\u0000\u0000\u01c2\u01c4\u0003\"\u0011"
          + "\u0000\u01c3\u01c5\u0003(\u0014\u0000\u01c4\u01c3\u0001\u0000\u0000\u0000"
          + "\u01c5\u01c6\u0001\u0000\u0000\u0000\u01c6\u01c4\u0001\u0000\u0000\u0000"
          + "\u01c6\u01c7\u0001\u0000\u0000\u0000\u01c7\u01cb\u0001\u0000\u0000\u0000"
          + "\u01c8\u01ca\u0003&\u0013\u0000\u01c9\u01c8\u0001\u0000\u0000\u0000\u01ca"
          + "\u01cd\u0001\u0000\u0000\u0000\u01cb\u01c9\u0001\u0000\u0000\u0000\u01cb"
          + "\u01cc\u0001\u0000\u0000\u0000\u01cc\u01ce\u0001\u0000\u0000\u0000\u01cd"
          + "\u01cb\u0001\u0000\u0000\u0000\u01ce\u01cf\u0005\u0003\u0000\u0000\u01cf"
          + "\u01d1\u0001\u0000\u0000\u0000\u01d0\u01ab\u0001\u0000\u0000\u0000\u01d0"
          + "\u01b6\u0001\u0000\u0000\u0000\u01d0\u01c1\u0001\u0000\u0000\u0000\u01d1"
          + ";\u0001\u0000\u0000\u0000\u01d2\u01ed\u0003:\u001d\u0000\u01d3\u01d4\u0005"
          + "\u0002\u0000\u0000\u01d4\u01d5\u0005@\u0000\u0000\u01d5\u01d7\u0005\u0002"
          + "\u0000\u0000\u01d6\u01d8\u0003\f\u0006\u0000\u01d7\u01d6\u0001\u0000\u0000"
          + "\u0000\u01d8\u01d9\u0001\u0000\u0000\u0000\u01d9\u01d7\u0001\u0000\u0000"
          + "\u0000\u01d9\u01da\u0001\u0000\u0000\u0000\u01da\u01db\u0001\u0000\u0000"
          + "\u0000\u01db\u01dc\u0005\u0003\u0000\u0000\u01dc\u01dd\u0005\u0002\u0000"
          + "\u0000\u01dd\u01df\u0003\"\u0011\u0000\u01de\u01e0\u0003(\u0014\u0000"
          + "\u01df\u01de\u0001\u0000\u0000\u0000\u01e0\u01e1\u0001\u0000\u0000\u0000"
          + "\u01e1\u01df\u0001\u0000\u0000\u0000\u01e1\u01e2\u0001\u0000\u0000\u0000"
          + "\u01e2\u01e6\u0001\u0000\u0000\u0000\u01e3\u01e5\u0003&\u0013\u0000\u01e4"
          + "\u01e3\u0001\u0000\u0000\u0000\u01e5\u01e8\u0001\u0000\u0000\u0000\u01e6"
          + "\u01e4\u0001\u0000\u0000\u0000\u01e6\u01e7\u0001\u0000\u0000\u0000\u01e7"
          + "\u01e9\u0001\u0000\u0000\u0000\u01e8\u01e6\u0001\u0000\u0000\u0000\u01e9"
          + "\u01ea\u0005\u0003\u0000\u0000\u01ea\u01eb\u0005\u0003\u0000\u0000\u01eb"
          + "\u01ed\u0001\u0000\u0000\u0000\u01ec\u01d2\u0001\u0000\u0000\u0000\u01ec"
          + "\u01d3\u0001\u0000\u0000\u0000\u01ed=\u0001\u0000\u0000\u0000\u01ee\u01ef"
          + "\u0005r\u0000\u0000\u01ef\u01f1\u0005\u0002\u0000\u0000\u01f0\u01f2\u0003"
          + "6\u001b\u0000\u01f1\u01f0\u0001\u0000\u0000\u0000\u01f2\u01f3\u0001\u0000"
          + "\u0000\u0000\u01f3\u01f1\u0001\u0000\u0000\u0000\u01f3\u01f4\u0001\u0000"
          + "\u0000\u0000\u01f4\u01f5\u0001\u0000\u0000\u0000\u01f5\u01f6\u0005\u0003"
          + "\u0000\u0000\u01f6\u020c\u0001\u0000\u0000\u0000\u01f7\u01f8\u0005Z\u0000"
          + "\u0000\u01f8\u01fa\u0005\u0002\u0000\u0000\u01f9\u01fb\u0003<\u001e\u0000"
          + "\u01fa\u01f9\u0001\u0000\u0000\u0000\u01fb\u01fc\u0001\u0000\u0000\u0000"
          + "\u01fc\u01fa\u0001\u0000\u0000\u0000\u01fc\u01fd\u0001\u0000\u0000\u0000"
          + "\u01fd\u01fe\u0001\u0000\u0000\u0000\u01fe\u01ff\u0005\u0003\u0000\u0000"
          + "\u01ff\u020c\u0001\u0000\u0000\u0000\u0200\u0201\u0005s\u0000\u0000\u0201"
          + "\u020c\u0003\u0016\u000b\u0000\u0202\u0203\u0005[\u0000\u0000\u0203\u020c"
          + "\u0003\u0016\u000b\u0000\u0204\u0205\u0005V\u0000\u0000\u0205\u020c\u0003"
          + "\u0016\u000b\u0000\u0206\u0207\u0005w\u0000\u0000\u0207\u020c\u0003\u0016"
          + "\u000b\u0000\u0208\u0209\u0005c\u0000\u0000\u0209\u020c\u0003\u0016\u000b"
          + "\u0000\u020a\u020c\u0003&\u0013\u0000\u020b\u01ee\u0001\u0000\u0000\u0000"
          + "\u020b\u01f7\u0001\u0000\u0000\u0000\u020b\u0200\u0001\u0000\u0000\u0000"
          + "\u020b\u0202\u0001\u0000\u0000\u0000\u020b\u0204\u0001\u0000\u0000\u0000"
          + "\u020b\u0206\u0001\u0000\u0000\u0000\u020b\u0208\u0001\u0000\u0000\u0000"
          + "\u020b\u020a\u0001\u0000\u0000\u0000\u020c?\u0001\u0000\u0000\u0000\u020d"
          + "\u020e\u0005\u0002\u0000\u0000\u020e\u020f\u0005\u0012\u0000\u0000\u020f"
          + "\u0211\u0003\f\u0006\u0000\u0210\u0212\u0003>\u001f\u0000\u0211\u0210"
          + "\u0001\u0000\u0000\u0000\u0212\u0213\u0001\u0000\u0000\u0000\u0213\u0211"
          + "\u0001\u0000\u0000\u0000\u0213\u0214\u0001\u0000\u0000\u0000\u0214\u0215"
          + "\u0001\u0000\u0000\u0000\u0215\u0216\u0005\u0003\u0000\u0000\u0216A\u0001"
          + "\u0000\u0000\u0000\u0217\u0218\u0005v\u0000\u0000\u0218\u021a\u0005\u0002"
          + "\u0000\u0000\u0219\u021b\u0003\f\u0006\u0000\u021a\u0219\u0001\u0000\u0000"
          + "\u0000\u021b\u021c\u0001\u0000\u0000\u0000\u021c\u021a\u0001\u0000\u0000"
          + "\u0000\u021c\u021d\u0001\u0000\u0000\u0000\u021d\u021e\u0001\u0000\u0000"
          + "\u0000\u021e\u021f\u0005\u0003\u0000\u0000\u021f\u022a\u0001\u0000\u0000"
          + "\u0000\u0220\u0221\u0005^\u0000\u0000\u0221\u022a\u0003\u0016\u000b\u0000"
          + "\u0222\u0223\u0005Y\u0000\u0000\u0223\u022a\u0003\u0016\u000b\u0000\u0224"
          + "\u0225\u0005w\u0000\u0000\u0225\u022a\u0003\u0016\u000b\u0000\u0226\u0227"
          + "\u0005c\u0000\u0000\u0227\u022a\u0003\u0016\u000b\u0000\u0228\u022a\u0003"
          + "&\u0013\u0000\u0229\u0217\u0001\u0000\u0000\u0000\u0229\u0220\u0001\u0000"
          + "\u0000\u0000\u0229\u0222\u0001\u0000\u0000\u0000\u0229\u0224\u0001\u0000"
          + "\u0000\u0000\u0229\u0226\u0001\u0000\u0000\u0000\u0229\u0228\u0001\u0000"
          + "\u0000\u0000\u022aC\u0001\u0000\u0000\u0000\u022b\u022c\u0005\u0002\u0000"
          + "\u0000\u022c\u022d\u0005\u000e\u0000\u0000\u022d\u022f\u0003\f\u0006\u0000"
          + "\u022e\u0230\u0003B!\u0000\u022f\u022e\u0001\u0000\u0000\u0000\u0230\u0231"
          + "\u0001\u0000\u0000\u0000\u0231\u022f\u0001\u0000\u0000\u0000\u0231\u0232"
          + "\u0001\u0000\u0000\u0000\u0232\u0233\u0001\u0000\u0000\u0000\u0233\u0234"
          + "\u0005\u0003\u0000\u0000\u0234E\u0001\u0000\u0000\u0000\u0235\u0236\u0005"
          + "\u0002\u0000\u0000\u0236\u0237\u0003\f\u0006\u0000\u0237\u0238\u0003\u000e"
          + "\u0007\u0000\u0238\u0239\u0005\u0003\u0000\u0000\u0239G\u0001\u0000\u0000"
          + "\u0000\u023a\u023b\u0005\u0002\u0000\u0000\u023b\u023c\u0003\f\u0006\u0000"
          + "\u023c\u023d\u0003(\u0014\u0000\u023d\u023e\u0005\u0003\u0000\u0000\u023e"
          + "I\u0001\u0000\u0000\u0000\u023f\u0240\u0005\u0002\u0000\u0000\u0240\u0244"
          + "\u0003\f\u0006\u0000\u0241\u0243\u0003H$\u0000\u0242\u0241\u0001\u0000"
          + "\u0000\u0000\u0243\u0246\u0001\u0000\u0000\u0000\u0244\u0242\u0001\u0000"
          + "\u0000\u0000\u0244\u0245\u0001\u0000\u0000\u0000\u0245\u0247\u0001\u0000"
          + "\u0000\u0000\u0246\u0244\u0001\u0000\u0000\u0000\u0247\u0248\u0005\u0003"
          + "\u0000\u0000\u0248K\u0001\u0000\u0000\u0000\u0249\u024b\u0005\u0002\u0000"
          + "\u0000\u024a\u024c\u0003J%\u0000\u024b\u024a\u0001\u0000\u0000\u0000\u024c"
          + "\u024d\u0001\u0000\u0000\u0000\u024d\u024b\u0001\u0000\u0000\u0000\u024d"
          + "\u024e\u0001\u0000\u0000\u0000\u024e\u024f\u0001\u0000\u0000\u0000\u024f"
          + "\u0250\u0005\u0003\u0000\u0000\u0250\u0264\u0001\u0000\u0000\u0000\u0251"
          + "\u0252\u0005\u0002\u0000\u0000\u0252\u0253\u0005@\u0000\u0000\u0253\u0255"
          + "\u0005\u0002\u0000\u0000\u0254\u0256\u0003\f\u0006\u0000\u0255\u0254\u0001"
          + "\u0000\u0000\u0000\u0256\u0257\u0001\u0000\u0000\u0000\u0257\u0255\u0001"
          + "\u0000\u0000\u0000\u0257\u0258\u0001\u0000\u0000\u0000\u0258\u0259\u0001"
          + "\u0000\u0000\u0000\u0259\u025a\u0005\u0003\u0000\u0000\u025a\u025c\u0005"
          + "\u0002\u0000\u0000\u025b\u025d\u0003J%\u0000\u025c\u025b\u0001\u0000\u0000"
          + "\u0000\u025d\u025e\u0001\u0000\u0000\u0000\u025e\u025c\u0001\u0000\u0000"
          + "\u0000\u025e\u025f\u0001\u0000\u0000\u0000\u025f\u0260\u0001\u0000\u0000"
          + "\u0000\u0260\u0261\u0005\u0003\u0000\u0000\u0261\u0262\u0005\u0003\u0000"
          + "\u0000\u0262\u0264\u0001\u0000\u0000\u0000\u0263\u0249\u0001\u0000\u0000"
          + "\u0000\u0263\u0251\u0001\u0000\u0000\u0000\u0264M\u0001\u0000\u0000\u0000"
          + "\u0265\u0266\u0005\u0002\u0000\u0000\u0266\u0267\u0003\f\u0006\u0000\u0267"
          + "\u026b\u0005\u0002\u0000\u0000\u0268\u026a\u0003.\u0017\u0000\u0269\u0268"
          + "\u0001\u0000\u0000\u0000\u026a\u026d\u0001\u0000\u0000\u0000\u026b\u0269"
          + "\u0001\u0000\u0000\u0000\u026b\u026c\u0001\u0000\u0000\u0000\u026c\u026e"
          + "\u0001\u0000\u0000\u0000\u026d\u026b\u0001\u0000\u0000\u0000\u026e\u026f"
          + "\u0005\u0003\u0000\u0000\u026f\u0270\u0003(\u0014\u0000\u0270\u0271\u0005"
          + "\u0003\u0000\u0000\u0271O\u0001\u0000\u0000\u0000\u0272\u0273\u0003\f"
          + "\u0006\u0000\u0273\u0277\u0005\u0002\u0000\u0000\u0274\u0276\u0003.\u0017"
          + "\u0000\u0275\u0274\u0001\u0000\u0000\u0000\u0276\u0279\u0001\u0000\u0000"
          + "\u0000\u0277\u0275\u0001\u0000\u0000\u0000\u0277\u0278\u0001\u0000\u0000"
          + "\u0000\u0278\u027a\u0001\u0000\u0000\u0000\u0279\u0277\u0001\u0000\u0000"
          + "\u0000\u027a\u027b\u0005\u0003\u0000\u0000\u027b\u027c\u0003(\u0014\u0000"
          + "\u027c\u027d\u00034\u001a\u0000\u027dQ\u0001\u0000\u0000\u0000\u027e\u0285"
          + "\u0003\f\u0006\u0000\u027f\u0280\u0005\u0002\u0000\u0000\u0280\u0281\u0005"
          + "\u0007\u0000\u0000\u0281\u0282\u0003\f\u0006\u0000\u0282\u0283\u0005\u0003"
          + "\u0000\u0000\u0283\u0285\u0001\u0000\u0000\u0000\u0284\u027e\u0001\u0000"
          + "\u0000\u0000\u0284\u027f\u0001\u0000\u0000\u0000\u0285S\u0001\u0000\u0000"
          + "\u0000\u0286\u0288\u0003\u0092I\u0000\u0287\u0286\u0001\u0000\u0000\u0000"
          + "\u0288\u028b\u0001\u0000\u0000\u0000\u0289\u0287\u0001\u0000\u0000\u0000"
          + "\u0289\u028a\u0001\u0000\u0000\u0000\u028aU\u0001\u0000\u0000\u0000\u028b"
          + "\u0289\u0001\u0000\u0000\u0000\u028c\u028d\u0005\u0017\u0000\u0000\u028d"
          + "\u028e\u00034\u001a\u0000\u028eW\u0001\u0000\u0000\u0000\u028f\u0290\u0005"
          + "\u0018\u0000\u0000\u0290Y\u0001\u0000\u0000\u0000\u0291\u0292\u0005\u0019"
          + "\u0000\u0000\u0292\u0296\u0005\u0002\u0000\u0000\u0293\u0295\u0003R)\u0000"
          + "\u0294\u0293\u0001\u0000\u0000\u0000\u0295\u0298\u0001\u0000\u0000\u0000"
          + "\u0296\u0294\u0001\u0000\u0000\u0000\u0296\u0297\u0001\u0000\u0000\u0000"
          + "\u0297\u0299\u0001\u0000\u0000\u0000\u0298\u0296\u0001\u0000\u0000\u0000"
          + "\u0299\u029a\u0005\u0003\u0000\u0000\u029a[\u0001\u0000\u0000\u0000\u029b"
          + "\u029c\u0005\u001a\u0000\u0000\u029c\u029d\u0003\f\u0006\u0000\u029d\u029e"
          + "\u0003(\u0014\u0000\u029e]\u0001\u0000\u0000\u0000\u029f\u02a0\u0005\u001b"
          + "\u0000\u0000\u02a0\u02a1\u0003\f\u0006\u0000\u02a1\u02a2\u0003L&\u0000"
          + "\u02a2\u0001\u0000\u0000\u0000\u02a3\u02a4\u0005\u001c\u0000\u0000\u02a4"
          + "\u02a6\u0005\u0002\u0000\u0000\u02a5\u02a7\u0003F#\u0000\u02a6\u02a5\u0001"
          + "\u0000\u0000\u0000\u02a7\u02a8\u0001\u0000\u0000\u0000\u02a8\u02a6\u0001"
          + "\u0000\u0000\u0000\u02a8\u02a9\u0001\u0000\u0000\u0000\u02a9\u02aa\u0001"
          + "\u0000\u0000\u0000\u02aa\u02ab\u0005\u0003\u0000\u0000\u02ab\u02ad\u0005"
          + "\u0002\u0000\u0000\u02ac\u02ae\u0003L&\u0000\u02ad\u02ac\u0001\u0000\u0000"
          + "\u0000\u02ae\u02af\u0001\u0000\u0000\u0000\u02af\u02ad\u0001\u0000\u0000"
          + "\u0000\u02af\u02b0\u0001\u0000\u0000\u0000\u02b0\u02b1\u0001\u0000\u0000"
          + "\u0000\u02b1\u02b2\u0005\u0003\u0000\u0000\u02b2a\u0001\u0000\u0000\u0000"
          + "\u02b3\u02b4\u0005\u001d\u0000\u0000\u02b4\u02b5\u0003\f\u0006\u0000\u02b5"
          + "\u02b9\u0005\u0002\u0000\u0000\u02b6\u02b8\u0003(\u0014\u0000\u02b7\u02b6"
          + "\u0001\u0000\u0000\u0000\u02b8\u02bb\u0001\u0000\u0000\u0000\u02b9\u02b7"
          + "\u0001\u0000\u0000\u0000\u02b9\u02ba\u0001\u0000\u0000\u0000\u02ba\u02bc"
          + "\u0001\u0000\u0000\u0000\u02bb\u02b9\u0001\u0000\u0000\u0000\u02bc\u02bd"
          + "\u0005\u0003\u0000\u0000\u02bd\u02be\u0003(\u0014\u0000\u02bec\u0001\u0000"
          + "\u0000\u0000\u02bf\u02c0\u0005\u001e\u0000\u0000\u02c0\u02c1\u0003\f\u0006"
          + "\u0000\u02c1\u02c2\u0003\u000e\u0007\u0000\u02c2e\u0001\u0000\u0000\u0000"
          + "\u02c3\u02c4\u0005\u001f\u0000\u0000\u02c4\u02c5\u0003P(\u0000\u02c5g"
          + "\u0001\u0000\u0000\u0000\u02c6\u02c7\u0005 \u0000\u0000\u02c7\u02c8\u0003"
          + "P(\u0000\u02c8i\u0001\u0000\u0000\u0000\u02c9\u02ca\u0005!\u0000\u0000"
          + "\u02ca\u02cc\u0005\u0002\u0000\u0000\u02cb\u02cd\u0003N\'\u0000\u02cc"
          + "\u02cb\u0001\u0000\u0000\u0000\u02cd\u02ce\u0001\u0000\u0000\u0000\u02ce"
          + "\u02cc\u0001\u0000\u0000\u0000\u02ce\u02cf\u0001\u0000\u0000\u0000\u02cf"
          + "\u02d0\u0001\u0000\u0000\u0000\u02d0\u02d1\u0005\u0003\u0000\u0000\u02d1"
          + "\u02d3\u0005\u0002\u0000\u0000\u02d2\u02d4\u00034\u001a\u0000\u02d3\u02d2"
          + "\u0001\u0000\u0000\u0000\u02d4\u02d5\u0001\u0000\u0000\u0000\u02d5\u02d3"
          + "\u0001\u0000\u0000\u0000\u02d5\u02d6\u0001\u0000\u0000\u0000\u02d6\u02d7"
          + "\u0001\u0000\u0000\u0000\u02d7\u02d8\u0005\u0003\u0000\u0000\u02d8k\u0001"
          + "\u0000\u0000\u0000\u02d9\u02da\u0005\"\u0000\u0000\u02da\u02db\u0003\f"
          + "\u0006\u0000\u02db\u02df\u0005\u0002\u0000\u0000\u02dc\u02de\u0003\f\u0006"
          + "\u0000\u02dd\u02dc\u0001\u0000\u0000\u0000\u02de\u02e1\u0001\u0000\u0000"
          + "\u0000\u02df\u02dd\u0001\u0000\u0000\u0000\u02df\u02e0\u0001\u0000\u0000"
          + "\u0000\u02e0\u02e2\u0001\u0000\u0000\u0000\u02e1\u02df\u0001\u0000\u0000"
          + "\u0000\u02e2\u02e3\u0005\u0003\u0000\u0000\u02e3\u02e4\u0003(\u0014\u0000"
          + "\u02e4m\u0001\u0000\u0000\u0000\u02e5\u02e6\u0005#\u0000\u0000\u02e6\u02e7"
          + "\u0003\u0016\u000b\u0000\u02e7o\u0001\u0000\u0000\u0000\u02e8\u02e9\u0005"
          + "$\u0000\u0000\u02e9q\u0001\u0000\u0000\u0000\u02ea\u02eb\u0005%\u0000"
          + "\u0000\u02ebs\u0001\u0000\u0000\u0000\u02ec\u02ed\u0005&\u0000\u0000\u02ed"
          + "u\u0001\u0000\u0000\u0000\u02ee\u02ef\u0005\'\u0000\u0000\u02ef\u02f0"
          + "\u0003\u0098L\u0000\u02f0w\u0001\u0000\u0000\u0000\u02f1\u02f2\u0005("
          + "\u0000\u0000\u02f2y\u0001\u0000\u0000\u0000\u02f3\u02f4\u0005)\u0000\u0000"
          + "\u02f4\u02f5\u0003\u001a\r\u0000\u02f5{\u0001\u0000\u0000\u0000\u02f6"
          + "\u02f7\u0005*\u0000\u0000\u02f7}\u0001\u0000\u0000\u0000\u02f8\u02f9\u0005"
          + "+\u0000\u0000\u02f9\u007f\u0001\u0000\u0000\u0000\u02fa\u02fb\u0005,\u0000"
          + "\u0000\u02fb\u0081\u0001\u0000\u0000\u0000\u02fc\u02fd\u0005-\u0000\u0000"
          + "\u02fd\u02ff\u0005\u0002\u0000\u0000\u02fe\u0300\u00034\u001a\u0000\u02ff"
          + "\u02fe\u0001\u0000\u0000\u0000\u0300\u0301\u0001\u0000\u0000\u0000\u0301"
          + "\u02ff\u0001\u0000\u0000\u0000\u0301\u0302\u0001\u0000\u0000\u0000\u0302"
          + "\u0303\u0001\u0000\u0000\u0000\u0303\u0304\u0005\u0003\u0000\u0000\u0304"
          + "\u0083\u0001\u0000\u0000\u0000\u0305\u0306\u0005.\u0000\u0000\u0306\u0307"
          + "\u0003\u000e\u0007\u0000\u0307\u0085\u0001\u0000\u0000\u0000\u0308\u0309"
          + "\u0005/\u0000\u0000\u0309\u030a\u0003\u000e\u0007\u0000\u030a\u0087\u0001"
          + "\u0000\u0000\u0000\u030b\u030c\u00050\u0000\u0000\u030c\u0089\u0001\u0000"
          + "\u0000\u0000\u030d\u030e\u00051\u0000\u0000\u030e\u008b\u0001\u0000\u0000"
          + "\u0000\u030f\u0310\u00052\u0000\u0000\u0310\u0311\u0003&\u0013\u0000\u0311"
          + "\u008d\u0001\u0000\u0000\u0000\u0312\u0313\u00053\u0000\u0000\u0313\u0314"
          + "\u0003\f\u0006\u0000\u0314\u008f\u0001\u0000\u0000\u0000\u0315\u0316\u0005"
          + "4\u0000\u0000\u0316\u0317\u0003\u0096K\u0000\u0317\u0091\u0001\u0000\u0000"
          + "\u0000\u0318\u0319\u0005\u0002\u0000\u0000\u0319\u031a\u0003V+\u0000\u031a"
          + "\u031b\u0005\u0003\u0000\u0000\u031b\u0391\u0001\u0000\u0000\u0000\u031c"
          + "\u031d\u0005\u0002\u0000\u0000\u031d\u031e\u0003X,\u0000\u031e\u031f\u0005"
          + "\u0003\u0000\u0000\u031f\u0391\u0001\u0000\u0000\u0000\u0320\u0321\u0005"
          + "\u0002\u0000\u0000\u0321\u0322\u0003Z-\u0000\u0322\u0323\u0005\u0003\u0000"
          + "\u0000\u0323\u0391\u0001\u0000\u0000\u0000\u0324\u0325\u0005\u0002\u0000"
          + "\u0000\u0325\u0326\u0003\\.\u0000\u0326\u0327\u0005\u0003\u0000\u0000"
          + "\u0327\u0391\u0001\u0000\u0000\u0000\u0328\u0329\u0005\u0002\u0000\u0000"
          + "\u0329\u032a\u0003^/\u0000\u032a\u032b\u0005\u0003\u0000\u0000\u032b\u0391"
          + "\u0001\u0000\u0000\u0000\u032c\u032d\u0005\u0002\u0000\u0000\u032d\u032e"
          + "\u0003`0\u0000\u032e\u032f\u0005\u0003\u0000\u0000\u032f\u0391\u0001\u0000"
          + "\u0000\u0000\u0330\u0331\u0005\u0002\u0000\u0000\u0331\u0332\u0003b1\u0000"
          + "\u0332\u0333\u0005\u0003\u0000\u0000\u0333\u0391\u0001\u0000\u0000\u0000"
          + "\u0334\u0335\u0005\u0002\u0000\u0000\u0335\u0336\u0003d2\u0000\u0336\u0337"
          + "\u0005\u0003\u0000\u0000\u0337\u0391\u0001\u0000\u0000\u0000\u0338\u0339"
          + "\u0005\u0002\u0000\u0000\u0339\u033a\u0003f3\u0000\u033a\u033b\u0005\u0003"
          + "\u0000\u0000\u033b\u0391\u0001\u0000\u0000\u0000\u033c\u033d\u0005\u0002"
          + "\u0000\u0000\u033d\u033e\u0003h4\u0000\u033e\u033f\u0005\u0003\u0000\u0000"
          + "\u033f\u0391\u0001\u0000\u0000\u0000\u0340\u0341\u0005\u0002\u0000\u0000"
          + "\u0341\u0342\u0003j5\u0000\u0342\u0343\u0005\u0003\u0000\u0000\u0343\u0391"
          + "\u0001\u0000\u0000\u0000\u0344\u0345\u0005\u0002\u0000\u0000\u0345\u0346"
          + "\u0003l6\u0000\u0346\u0347\u0005\u0003\u0000\u0000\u0347\u0391\u0001\u0000"
          + "\u0000\u0000\u0348\u0349\u0005\u0002\u0000\u0000\u0349\u034a\u0003n7\u0000"
          + "\u034a\u034b\u0005\u0003\u0000\u0000\u034b\u0391\u0001\u0000\u0000\u0000"
          + "\u034c\u034d\u0005\u0002\u0000\u0000\u034d\u034e\u0003p8\u0000\u034e\u034f"
          + "\u0005\u0003\u0000\u0000\u034f\u0391\u0001\u0000\u0000\u0000\u0350\u0351"
          + "\u0005\u0002\u0000\u0000\u0351\u0352\u0003r9\u0000\u0352\u0353\u0005\u0003"
          + "\u0000\u0000\u0353\u0391\u0001\u0000\u0000\u0000\u0354\u0355\u0005\u0002"
          + "\u0000\u0000\u0355\u0356\u0003t:\u0000\u0356\u0357\u0005\u0003\u0000\u0000"
          + "\u0357\u0391\u0001\u0000\u0000\u0000\u0358\u0359\u0005\u0002\u0000\u0000"
          + "\u0359\u035a\u0003v;\u0000\u035a\u035b\u0005\u0003\u0000\u0000\u035b\u0391"
          + "\u0001\u0000\u0000\u0000\u035c\u035d\u0005\u0002\u0000\u0000\u035d\u035e"
          + "\u0003x<\u0000\u035e\u035f\u0005\u0003\u0000\u0000\u035f\u0391\u0001\u0000"
          + "\u0000\u0000\u0360\u0361\u0005\u0002\u0000\u0000\u0361\u0362\u0003z=\u0000"
          + "\u0362\u0363\u0005\u0003\u0000\u0000\u0363\u0391\u0001\u0000\u0000\u0000"
          + "\u0364\u0365\u0005\u0002\u0000\u0000\u0365\u0366\u0003|>\u0000\u0366\u0367"
          + "\u0005\u0003\u0000\u0000\u0367\u0391\u0001\u0000\u0000\u0000\u0368\u0369"
          + "\u0005\u0002\u0000\u0000\u0369\u036a\u0003~?\u0000\u036a\u036b\u0005\u0003"
          + "\u0000\u0000\u036b\u0391\u0001\u0000\u0000\u0000\u036c\u036d\u0005\u0002"
          + "\u0000\u0000\u036d\u036e\u0003\u0080@\u0000\u036e\u036f\u0005\u0003\u0000"
          + "\u0000\u036f\u0391\u0001\u0000\u0000\u0000\u0370\u0371\u0005\u0002\u0000"
          + "\u0000\u0371\u0372\u0003\u0082A\u0000\u0372\u0373\u0005\u0003\u0000\u0000"
          + "\u0373\u0391\u0001\u0000\u0000\u0000\u0374\u0375\u0005\u0002\u0000\u0000"
          + "\u0375\u0376\u0003\u0084B\u0000\u0376\u0377\u0005\u0003\u0000\u0000\u0377"
          + "\u0391\u0001\u0000\u0000\u0000\u0378\u0379\u0005\u0002\u0000\u0000\u0379"
          + "\u037a\u0003\u0086C\u0000\u037a\u037b\u0005\u0003\u0000\u0000\u037b\u0391"
          + "\u0001\u0000\u0000\u0000\u037c\u037d\u0005\u0002\u0000\u0000\u037d\u037e"
          + "\u0003\u0088D\u0000\u037e\u037f\u0005\u0003\u0000\u0000\u037f\u0391\u0001"
          + "\u0000\u0000\u0000\u0380\u0381\u0005\u0002\u0000\u0000\u0381\u0382\u0003"
          + "\u008aE\u0000\u0382\u0383\u0005\u0003\u0000\u0000\u0383\u0391\u0001\u0000"
          + "\u0000\u0000\u0384\u0385\u0005\u0002\u0000\u0000\u0385\u0386\u0003\u008c"
          + "F\u0000\u0386\u0387\u0005\u0003\u0000\u0000\u0387\u0391\u0001\u0000\u0000"
          + "\u0000\u0388\u0389\u0005\u0002\u0000\u0000\u0389\u038a\u0003\u008eG\u0000"
          + "\u038a\u038b\u0005\u0003\u0000\u0000\u038b\u0391\u0001\u0000\u0000\u0000"
          + "\u038c\u038d\u0005\u0002\u0000\u0000\u038d\u038e\u0003\u0090H\u0000\u038e"
          + "\u038f\u0005\u0003\u0000\u0000\u038f\u0391\u0001\u0000\u0000\u0000\u0390"
          + "\u0318\u0001\u0000\u0000\u0000\u0390\u031c\u0001\u0000\u0000\u0000\u0390"
          + "\u0320\u0001\u0000\u0000\u0000\u0390\u0324\u0001\u0000\u0000\u0000\u0390"
          + "\u0328\u0001\u0000\u0000\u0000\u0390\u032c\u0001\u0000\u0000\u0000\u0390"
          + "\u0330\u0001\u0000\u0000\u0000\u0390\u0334\u0001\u0000\u0000\u0000\u0390"
          + "\u0338\u0001\u0000\u0000\u0000\u0390\u033c\u0001\u0000\u0000\u0000\u0390"
          + "\u0340\u0001\u0000\u0000\u0000\u0390\u0344\u0001\u0000\u0000\u0000\u0390"
          + "\u0348\u0001\u0000\u0000\u0000\u0390\u034c\u0001\u0000\u0000\u0000\u0390"
          + "\u0350\u0001\u0000\u0000\u0000\u0390\u0354\u0001\u0000\u0000\u0000\u0390"
          + "\u0358\u0001\u0000\u0000\u0000\u0390\u035c\u0001\u0000\u0000\u0000\u0390"
          + "\u0360\u0001\u0000\u0000\u0000\u0390\u0364\u0001\u0000\u0000\u0000\u0390"
          + "\u0368\u0001\u0000\u0000\u0000\u0390\u036c\u0001\u0000\u0000\u0000\u0390"
          + "\u0370\u0001\u0000\u0000\u0000\u0390\u0374\u0001\u0000\u0000\u0000\u0390"
          + "\u0378\u0001\u0000\u0000\u0000\u0390\u037c\u0001\u0000\u0000\u0000\u0390"
          + "\u0380\u0001\u0000\u0000\u0000\u0390\u0384\u0001\u0000\u0000\u0000\u0390"
          + "\u0388\u0001\u0000\u0000\u0000\u0390\u038c\u0001\u0000\u0000\u0000\u0391"
          + "\u0093\u0001\u0000\u0000\u0000\u0392\u0393\u0007\u0004\u0000\u0000\u0393"
          + "\u0095\u0001\u0000\u0000\u0000\u0394\u0395\u0005W\u0000\u0000\u0395\u03b2"
          + "\u0003\u0016\u000b\u0000\u0396\u0397\u0005\\\u0000\u0000\u0397\u03b2\u0003"
          + "\u0094J\u0000\u0398\u0399\u0005]\u0000\u0000\u0399\u03b2\u0003\u0094J"
          + "\u0000\u039a\u039b\u0005e\u0000\u0000\u039b\u03b2\u0003\u0094J\u0000\u039c"
          + "\u039d\u0005f\u0000\u0000\u039d\u03b2\u0003\u0094J\u0000\u039e\u039f\u0005"
          + "g\u0000\u0000\u039f\u03b2\u0003\u0094J\u0000\u03a0\u03a1\u0005h\u0000"
          + "\u0000\u03a1\u03b2\u0003\u0094J\u0000\u03a2\u03a3\u0005i\u0000\u0000\u03a3"
          + "\u03b2\u0003\u0094J\u0000\u03a4\u03a5\u0005j\u0000\u0000\u03a5\u03b2\u0003"
          + "\u0094J\u0000\u03a6\u03a7\u0005k\u0000\u0000\u03a7\u03b2\u0003\u0094J"
          + "\u0000\u03a8\u03a9\u0005l\u0000\u0000\u03a9\u03b2\u0003\u000e\u0007\u0000"
          + "\u03aa\u03ab\u0005n\u0000\u0000\u03ab\u03b2\u0003\u0016\u000b\u0000\u03ac"
          + "\u03ad\u0005o\u0000\u0000\u03ad\u03b2\u0003\u000e\u0007\u0000\u03ae\u03af"
          + "\u0005x\u0000\u0000\u03af\u03b2\u0003\u000e\u0007\u0000\u03b0\u03b2\u0003"
          + "&\u0013\u0000\u03b1\u0394\u0001\u0000\u0000\u0000\u03b1\u0396\u0001\u0000"
          + "\u0000\u0000\u03b1\u0398\u0001\u0000\u0000\u0000\u03b1\u039a\u0001\u0000"
          + "\u0000\u0000\u03b1\u039c\u0001\u0000\u0000\u0000\u03b1\u039e\u0001\u0000"
          + "\u0000\u0000\u03b1\u03a0\u0001\u0000\u0000\u0000\u03b1\u03a2\u0001\u0000"
          + "\u0000\u0000\u03b1\u03a4\u0001\u0000\u0000\u0000\u03b1\u03a6\u0001\u0000"
          + "\u0000\u0000\u03b1\u03a8\u0001\u0000\u0000\u0000\u03b1\u03aa\u0001\u0000"
          + "\u0000\u0000\u03b1\u03ac\u0001\u0000\u0000\u0000\u03b1\u03ae\u0001\u0000"
          + "\u0000\u0000\u03b1\u03b0\u0001\u0000\u0000\u0000\u03b2\u0097\u0001\u0000"
          + "\u0000\u0000\u03b3\u03bc\u0005Q\u0000\u0000\u03b4\u03bc\u0005R\u0000\u0000"
          + "\u03b5\u03bc\u0005S\u0000\u0000\u03b6\u03bc\u0005X\u0000\u0000\u03b7\u03bc"
          + "\u0005b\u0000\u0000\u03b8\u03bc\u0005m\u0000\u0000\u03b9\u03bc\u0005y"
          + "\u0000\u0000\u03ba\u03bc\u0003\u001a\r\u0000\u03bb\u03b3\u0001\u0000\u0000"
          + "\u0000\u03bb\u03b4\u0001\u0000\u0000\u0000\u03bb\u03b5\u0001\u0000\u0000"
          + "\u0000\u03bb\u03b6\u0001\u0000\u0000\u0000\u03bb\u03b7\u0001\u0000\u0000"
          + "\u0000\u03bb\u03b8\u0001\u0000\u0000\u0000\u03bb\u03b9\u0001\u0000\u0000"
          + "\u0000\u03bb\u03ba\u0001\u0000\u0000\u0000\u03bc\u0099\u0001\u0000\u0000"
          + "\u0000\u03bd\u03be\u0007\u0005\u0000\u0000\u03be\u009b\u0001\u0000\u0000"
          + "\u0000\u03bf\u03c3\u0005\u000f\u0000\u0000\u03c0\u03c3\u0005\r\u0000\u0000"
          + "\u03c1\u03c3\u0003\u001e\u000f\u0000\u03c2\u03bf\u0001\u0000\u0000\u0000"
          + "\u03c2\u03c0\u0001\u0000\u0000\u0000\u03c2\u03c1\u0001\u0000\u0000\u0000"
          + "\u03c3\u009d\u0001\u0000\u0000\u0000\u03c4\u03c5\u0005\u0002\u0000\u0000"
          + "\u03c5\u03c6\u0003f3\u0000\u03c6\u03c7\u0005\u0003\u0000\u0000\u03c7\u03d1"
          + "\u0001\u0000\u0000\u0000\u03c8\u03c9\u0005\u0002\u0000\u0000\u03c9\u03ca"
          + "\u0003h4\u0000\u03ca\u03cb\u0005\u0003\u0000\u0000\u03cb\u03d1\u0001\u0000"
          + "\u0000\u0000\u03cc\u03cd\u0005\u0002\u0000\u0000\u03cd\u03ce\u0003j5\u0000"
          + "\u03ce\u03cf\u0005\u0003\u0000\u0000\u03cf\u03d1\u0001\u0000\u0000\u0000"
          + "\u03d0\u03c4\u0001\u0000\u0000\u0000\u03d0\u03c8\u0001\u0000\u0000\u0000"
          + "\u03d0\u03cc\u0001\u0000\u0000\u0000\u03d1\u009f\u0001\u0000\u0000\u0000"
          + "\u03d2\u03d3\u0005R\u0000\u0000\u03d3\u03e0\u0003\u000e\u0007\u0000\u03d4"
          + "\u03d5\u0005S\u0000\u0000\u03d5\u03e0\u0003\u0016\u000b\u0000\u03d6\u03d7"
          + "\u0005X\u0000\u0000\u03d7\u03e0\u0003\u009aM\u0000\u03d8\u03d9\u0005b"
          + "\u0000\u0000\u03d9\u03e0\u0003\u0016\u000b\u0000\u03da\u03db\u0005m\u0000"
          + "\u0000\u03db\u03e0\u0003\u009cN\u0000\u03dc\u03dd\u0005y\u0000\u0000\u03dd"
          + "\u03e0\u0003\u0016\u000b\u0000\u03de\u03e0\u0003&\u0013\u0000\u03df\u03d2"
          + "\u0001\u0000\u0000\u0000\u03df\u03d4\u0001\u0000\u0000\u0000\u03df\u03d6"
          + "\u0001\u0000\u0000\u0000\u03df\u03d8\u0001\u0000\u0000\u0000\u03df\u03da"
          + "\u0001\u0000\u0000\u0000\u03df\u03dc\u0001\u0000\u0000\u0000\u03df\u03de"
          + "\u0001\u0000\u0000\u0000\u03e0\u00a1\u0001\u0000\u0000\u0000\u03e1\u03e2"
          + "\u0005\u0002\u0000\u0000\u03e2\u03e3\u00034\u001a\u0000\u03e3\u03e4\u0003"
          + "4\u001a\u0000\u03e4\u03e5\u0005\u0003\u0000\u0000\u03e5\u00a3\u0001\u0000"
          + "\u0000\u0000\u03e6\u03e7\u0005\u0002\u0000\u0000\u03e7\u03e8\u0003\f\u0006"
          + "\u0000\u03e8\u03e9\u0003\u0094J\u0000\u03e9\u03ea\u0005\u0003\u0000\u0000"
          + "\u03ea\u00a5\u0001\u0000\u0000\u0000\u03eb\u03ec\u0007\u0006\u0000\u0000"
          + "\u03ec\u00a7\u0001\u0000\u0000\u0000\u03ed\u03ee\u0003\u0016\u000b\u0000"
          + "\u03ee\u00a9\u0001\u0000\u0000\u0000\u03ef\u03f3\u0005\u0002\u0000\u0000"
          + "\u03f0\u03f2\u00034\u001a\u0000\u03f1\u03f0\u0001\u0000\u0000\u0000\u03f2"
          + "\u03f5\u0001\u0000\u0000\u0000\u03f3\u03f1\u0001\u0000\u0000\u0000\u03f3"
          + "\u03f4\u0001\u0000\u0000\u0000\u03f4\u03f6\u0001\u0000\u0000\u0000\u03f5"
          + "\u03f3\u0001\u0000\u0000\u0000\u03f6\u03f7\u0005\u0003\u0000\u0000\u03f7"
          + "\u00ab\u0001\u0000\u0000\u0000\u03f8\u03fc\u0005\u0002\u0000\u0000\u03f9"
          + "\u03fb\u0003\u00a4R\u0000\u03fa\u03f9\u0001\u0000\u0000\u0000\u03fb\u03fe"
          + "\u0001\u0000\u0000\u0000\u03fc\u03fa\u0001\u0000\u0000\u0000\u03fc\u03fd"
          + "\u0001\u0000\u0000\u0000\u03fd\u03ff\u0001\u0000\u0000\u0000\u03fe\u03fc"
          + "\u0001\u0000\u0000\u0000\u03ff\u0400\u0005\u0003\u0000\u0000\u0400\u00ad"
          + "\u0001\u0000\u0000\u0000\u0401\u0403\u0005\u0002\u0000\u0000\u0402\u0404"
          + "\u0003\u00a0P\u0000\u0403\u0402\u0001\u0000\u0000\u0000\u0404\u0405\u0001"
          + "\u0000\u0000\u0000\u0405\u0403\u0001\u0000\u0000\u0000\u0405\u0406\u0001"
          + "\u0000\u0000\u0000\u0406\u0407\u0001\u0000\u0000\u0000\u0407\u0408\u0005"
          + "\u0003\u0000\u0000\u0408\u00af\u0001\u0000\u0000\u0000\u0409\u040a\u0005"
          + "\u0002\u0000\u0000\u040a\u040e\u0005z\u0000\u0000\u040b\u040d\u0003\u009e"
          + "O\u0000\u040c\u040b\u0001\u0000\u0000\u0000\u040d\u0410\u0001\u0000\u0000"
          + "\u0000\u040e\u040c\u0001\u0000\u0000\u0000\u040e\u040f\u0001\u0000\u0000"
          + "\u0000\u040f\u0411\u0001\u0000\u0000\u0000\u0410\u040e\u0001\u0000\u0000"
          + "\u0000\u0411\u041b\u0005\u0003\u0000\u0000\u0412\u0416\u0005\u0002\u0000"
          + "\u0000\u0413\u0415\u0003\u009eO\u0000\u0414\u0413\u0001\u0000\u0000\u0000"
          + "\u0415\u0418\u0001\u0000\u0000\u0000\u0416\u0414\u0001\u0000\u0000\u0000"
          + "\u0416\u0417\u0001\u0000\u0000\u0000\u0417\u0419\u0001\u0000\u0000\u0000"
          + "\u0418\u0416\u0001\u0000\u0000\u0000\u0419\u041b\u0005\u0003\u0000\u0000"
          + "\u041a\u0409\u0001\u0000\u0000\u0000\u041a\u0412\u0001\u0000\u0000\u0000"
          + "\u041b\u00b1\u0001\u0000\u0000\u0000\u041c\u041d\u0003$\u0012\u0000\u041d"
          + "\u00b3\u0001\u0000\u0000\u0000\u041e\u041f\u0003\u001e\u000f\u0000\u041f"
          + "\u00b5\u0001\u0000\u0000\u0000\u0420\u0424\u0005\u0002\u0000\u0000\u0421"
          + "\u0423\u0003\f\u0006\u0000\u0422\u0421\u0001\u0000\u0000\u0000\u0423\u0426"
          + "\u0001\u0000\u0000\u0000\u0424\u0422\u0001\u0000\u0000\u0000\u0424\u0425"
          + "\u0001\u0000\u0000\u0000\u0425\u0427\u0001\u0000\u0000\u0000\u0426\u0424"
          + "\u0001\u0000\u0000\u0000\u0427\u0428\u0005\u0003\u0000\u0000\u0428\u00b7"
          + "\u0001\u0000\u0000\u0000\u0429\u042d\u0005\u0002\u0000\u0000\u042a\u042c"
          + "\u0003\f\u0006\u0000\u042b\u042a\u0001\u0000\u0000\u0000\u042c\u042f\u0001"
          + "\u0000\u0000\u0000\u042d\u042b\u0001\u0000\u0000\u0000\u042d\u042e\u0001"
          + "\u0000\u0000\u0000\u042e\u0430\u0001\u0000\u0000\u0000\u042f\u042d\u0001"
          + "\u0000\u0000\u0000\u0430\u0431\u0005\u0003\u0000\u0000\u0431\u00b9\u0001"
          + "\u0000\u0000\u0000\u0432\u0434\u0005\u0002\u0000\u0000\u0433\u0435\u0003"
          + "\u00a2Q\u0000\u0434\u0433\u0001\u0000\u0000\u0000\u0435\u0436\u0001\u0000"
          + "\u0000\u0000\u0436\u0434\u0001\u0000\u0000\u0000\u0436\u0437\u0001\u0000"
          + "\u0000\u0000\u0437\u0438\u0001\u0000\u0000\u0000\u0438\u0439\u0005\u0003"
          + "\u0000\u0000\u0439\u00bb\u0001\u0000\u0000\u0000\u043a\u0446\u0003\u00a6"
          + "S\u0000\u043b\u0446\u0003\u00a8T\u0000\u043c\u0446\u0003\u00aaU\u0000"
          + "\u043d\u0446\u0003\u00acV\u0000\u043e\u0446\u0003\u00aeW\u0000\u043f\u0446"
          + "\u0003\u00b0X\u0000\u0440\u0446\u0003\u00b2Y\u0000\u0441\u0446\u0003\u00b4"
          + "Z\u0000\u0442\u0446\u0003\u00b6[\u0000\u0443\u0446\u0003\u00b8\\\u0000"
          + "\u0444\u0446\u0003\u00ba]\u0000\u0445\u043a\u0001\u0000\u0000\u0000\u0445"
          + "\u043b\u0001\u0000\u0000\u0000\u0445\u043c\u0001\u0000\u0000\u0000\u0445"
          + "\u043d\u0001\u0000\u0000\u0000\u0445\u043e\u0001\u0000\u0000\u0000\u0445"
          + "\u043f\u0001\u0000\u0000\u0000\u0445\u0440\u0001\u0000\u0000\u0000\u0445"
          + "\u0441\u0001\u0000\u0000\u0000\u0445\u0442\u0001\u0000\u0000\u0000\u0445"
          + "\u0443\u0001\u0000\u0000\u0000\u0445\u0444\u0001\u0000\u0000\u0000\u0446"
          + "\u00bd\u0001\u0000\u0000\u0000\u0447\u0450\u0005\u0011\u0000\u0000\u0448"
          + "\u0450\u0003\u00bc^\u0000\u0449\u0450\u0005\u0015\u0000\u0000\u044a\u044b"
          + "\u0005\u0002\u0000\u0000\u044b\u044c\u0005\n\u0000\u0000\u044c\u044d\u0003"
          + "\u0016\u000b\u0000\u044d\u044e\u0005\u0003\u0000\u0000\u044e\u0450\u0001"
          + "\u0000\u0000\u0000\u044f\u0447\u0001\u0000\u0000\u0000\u044f\u0448\u0001"
          + "\u0000\u0000\u0000\u044f\u0449\u0001\u0000\u0000\u0000\u044f\u044a\u0001"
          + "\u0000\u0000\u0000\u0450\u00bf\u0001\u0000\u0000\u0000L\u00cc\u00d2\u00dc"
          + "\u00ed\u00f5\u00fe\u0102\u0106\u010f\u0113\u011b\u011f\u0125\u012d\u0131"
          + "\u013a\u014c\u0150\u015e\u0168\u0174\u0180\u018d\u0198\u019c\u01a4\u01b1"
          + "\u01bc\u01c6\u01cb\u01d0\u01d9\u01e1\u01e6\u01ec\u01f3\u01fc\u020b\u0213"
          + "\u021c\u0229\u0231\u0244\u024d\u0257\u025e\u0263\u026b\u0277\u0284\u0289"
          + "\u0296\u02a8\u02af\u02b9\u02ce\u02d5\u02df\u0301\u0390\u03b1\u03bb\u03c2"
          + "\u03d0\u03df\u03f3\u03fc\u0405\u040e\u0416\u041a\u0424\u042d\u0436\u0445"
          + "\u044f";
  public static final ATN ATN = new ATNDeserializer().deserialize(serializedATN.toCharArray());

  static {
    decisionToDFA = new DFA[ATN.getNumberOfDecisions()];
    for (int i = 0; i < ATN.getNumberOfDecisions(); i++) {
      decisionToDFA[i] = new DFA(ATN.getDecisionState(i), i);
    }
  }
}
