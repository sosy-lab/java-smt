/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

// Generated from Smtlib.g4 by ANTLR 4.13.2
package org.sosy_lab.java_smt.basicimpl.parser;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
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
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.antlr.v4.runtime.tree.TerminalNode;

@SuppressWarnings({
  "all",
  "warnings",
  "unchecked",
  "unused",
  "cast",
  "CheckReturnValue",
  "this-escape"
})
@SuppressFBWarnings({"NM_METHOD_NAMING_CONVENTION", "SF_SWITCH_NO_DEFAULT"})
public class SmtlibParser extends Parser {
  static {
    RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION);
  }

  static final DFA[] _decisionToDFA;
  protected static final PredictionContextCache _sharedContextCache = new PredictionContextCache();
  public static final int T__0 = 1,
      T__1 = 2,
      T__2 = 3,
      T__3 = 4,
      T__4 = 5,
      T__5 = 6,
      T__6 = 7,
      T__7 = 8,
      T__8 = 9,
      T__9 = 10,
      T__10 = 11,
      T__11 = 12,
      T__12 = 13,
      T__13 = 14,
      T__14 = 15,
      T__15 = 16,
      T__16 = 17,
      T__17 = 18,
      T__18 = 19,
      T__19 = 20,
      T__20 = 21,
      T__21 = 22,
      T__22 = 23,
      T__23 = 24,
      T__24 = 25,
      T__25 = 26,
      T__26 = 27,
      T__27 = 28,
      T__28 = 29,
      T__29 = 30,
      T__30 = 31,
      T__31 = 32,
      T__32 = 33,
      T__33 = 34,
      T__34 = 35,
      T__35 = 36,
      T__36 = 37,
      T__37 = 38,
      T__38 = 39,
      T__39 = 40,
      T__40 = 41,
      T__41 = 42,
      T__42 = 43,
      T__43 = 44,
      Comment = 45,
      White = 46,
      Binary = 47,
      HexaDecimal = 48,
      Numeral = 49,
      Decimal = 50,
      String = 51,
      Simple = 52,
      Quoted = 53,
      Keyword = 54;
  public static final int RULE_boolean = 0,
      RULE_bitvec = 1,
      RULE_float = 2,
      RULE_integer = 3,
      RULE_real = 4,
      RULE_string = 5,
      RULE_literal = 6,
      RULE_symbol = 7,
      RULE_keyword = 8,
      RULE_sort = 9,
      RULE_quantifier = 10,
      RULE_sortedVar = 11,
      RULE_binding = 12,
      RULE_attribute = 13,
      RULE_expr = 14,
      RULE_setInfo = 15,
      RULE_setOption = 16,
      RULE_setLogic = 17,
      RULE_declare = 18,
      RULE_define = 19,
      RULE_push = 20,
      RULE_pop = 21,
      RULE_assert = 22,
      RULE_getAssertions = 23,
      RULE_check = 24,
      RULE_getModel = 25,
      RULE_getCore = 26,
      RULE_getValue = 27,
      RULE_reset = 28,
      RULE_exit = 29,
      RULE_command = 30,
      RULE_smtlib = 31;

  private static String[] makeRuleNames() {
    return new String[] {
      "boolean", "bitvec", "float", "integer", "real", "string", "literal",
      "symbol", "keyword", "sort", "quantifier", "sortedVar", "binding", "attribute",
      "expr", "setInfo", "setOption", "setLogic", "declare", "define", "push",
      "pop", "assert", "getAssertions", "check", "getModel", "getCore", "getValue",
      "reset", "exit", "command", "smtlib"
    };
  }

  static final String[] ruleNames = makeRuleNames();

  private static String[] makeLiteralNames() {
    return new String[] {
      null,
      "'true'",
      "'false'",
      "'('",
      "'fp'",
      "')'",
      "'Bool'",
      "'Int'",
      "'Real'",
      "'String'",
      "'RegLan'",
      "'_'",
      "'BitVec'",
      "'RoundingMode'",
      "'Float16'",
      "'Float32'",
      "'Float64'",
      "'Float128'",
      "'FloatingPoint'",
      "'Array'",
      "'forall'",
      "'exists'",
      "'as'",
      "'!'",
      "'let'",
      "'set-info'",
      "'set-option'",
      "'set-logic'",
      "'declare-const'",
      "'declare-fun'",
      "'define-const'",
      "'define-fun'",
      "'push'",
      "'pop'",
      "'assert'",
      "'get-assertions'",
      "'check-sat'",
      "'check-sat-assuming'",
      "'get-model'",
      "'get-unsat-core'",
      "'get-unsat-assumptions'",
      "'get-value'",
      "'reset'",
      "'reset-assertions'",
      "'exit'"
    };
  }

  private static final String[] _LITERAL_NAMES = makeLiteralNames();

  private static String[] makeSymbolicNames() {
    return new String[] {
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
      null,
      null,
      null,
      "Comment",
      "White",
      "Binary",
      "HexaDecimal",
      "Numeral",
      "Decimal",
      "String",
      "Simple",
      "Quoted",
      "Keyword"
    };
  }

  private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
  public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

  /**
   * @deprecated Use {@link #VOCABULARY} instead.
   */
  @Deprecated static final String[] tokenNames;

  static {
    tokenNames = new String[_SYMBOLIC_NAMES.length];
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
    return "Smtlib.g4";
  }

  @Override
  public String[] getRuleNames() {
    return ruleNames;
  }

  @Override
  public String getSerializedATN() {
    return _serializedATN;
  }

  @Override
  public ATN getATN() {
    return _ATN;
  }

  public SmtlibParser(TokenStream input) {
    super(input);
    _interp = new ParserATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
  }

  @SuppressWarnings("CheckReturnValue")
  public static class BooleanContext extends ParserRuleContext {
    public BooleanContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_boolean;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitBoolean(this);
      else return visitor.visitChildren(this);
    }
  }

  public final BooleanContext boolean_() throws RecognitionException {
    BooleanContext _localctx = new BooleanContext(_ctx, getState());
    enterRule(_localctx, 0, RULE_boolean);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(64);
        _la = _input.LA(1);
        if (!(_la == T__0 || _la == T__1)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class BitvecContext extends ParserRuleContext {
    public TerminalNode Binary() {
      return getToken(SmtlibParser.Binary, 0);
    }

    public TerminalNode HexaDecimal() {
      return getToken(SmtlibParser.HexaDecimal, 0);
    }

    public BitvecContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_bitvec;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitBitvec(this);
      else return visitor.visitChildren(this);
    }
  }

  public final BitvecContext bitvec() throws RecognitionException {
    BitvecContext _localctx = new BitvecContext(_ctx, getState());
    enterRule(_localctx, 2, RULE_bitvec);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(66);
        _la = _input.LA(1);
        if (!(_la == Binary || _la == HexaDecimal)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class FloatContext extends ParserRuleContext {
    public List<BitvecContext> bitvec() {
      return getRuleContexts(BitvecContext.class);
    }

    public BitvecContext bitvec(int i) {
      return getRuleContext(BitvecContext.class, i);
    }

    public FloatContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_float;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitFloat(this);
      else return visitor.visitChildren(this);
    }
  }

  public final FloatContext float_() throws RecognitionException {
    FloatContext _localctx = new FloatContext(_ctx, getState());
    enterRule(_localctx, 4, RULE_float);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(68);
        match(T__2);
        setState(69);
        match(T__3);
        setState(70);
        bitvec();
        setState(71);
        bitvec();
        setState(72);
        bitvec();
        setState(73);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IntegerContext extends ParserRuleContext {
    public TerminalNode Numeral() {
      return getToken(SmtlibParser.Numeral, 0);
    }

    public IntegerContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_integer;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitInteger(this);
      else return visitor.visitChildren(this);
    }
  }

  public final IntegerContext integer() throws RecognitionException {
    IntegerContext _localctx = new IntegerContext(_ctx, getState());
    enterRule(_localctx, 6, RULE_integer);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(75);
        match(Numeral);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class RealContext extends ParserRuleContext {
    public TerminalNode Decimal() {
      return getToken(SmtlibParser.Decimal, 0);
    }

    public RealContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_real;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitReal(this);
      else return visitor.visitChildren(this);
    }
  }

  public final RealContext real() throws RecognitionException {
    RealContext _localctx = new RealContext(_ctx, getState());
    enterRule(_localctx, 8, RULE_real);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(77);
        match(Decimal);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class StringContext extends ParserRuleContext {
    public TerminalNode String() {
      return getToken(SmtlibParser.String, 0);
    }

    public StringContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_string;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitString(this);
      else return visitor.visitChildren(this);
    }
  }

  public final StringContext string() throws RecognitionException {
    StringContext _localctx = new StringContext(_ctx, getState());
    enterRule(_localctx, 10, RULE_string);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(79);
        match(String);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LiteralContext extends ParserRuleContext {
    public BooleanContext boolean_() {
      return getRuleContext(BooleanContext.class, 0);
    }

    public IntegerContext integer() {
      return getRuleContext(IntegerContext.class, 0);
    }

    public RealContext real() {
      return getRuleContext(RealContext.class, 0);
    }

    public BitvecContext bitvec() {
      return getRuleContext(BitvecContext.class, 0);
    }

    public FloatContext float_() {
      return getRuleContext(FloatContext.class, 0);
    }

    public StringContext string() {
      return getRuleContext(StringContext.class, 0);
    }

    public LiteralContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_literal;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitLiteral(this);
      else return visitor.visitChildren(this);
    }
  }

  public final LiteralContext literal() throws RecognitionException {
    LiteralContext _localctx = new LiteralContext(_ctx, getState());
    enterRule(_localctx, 12, RULE_literal);
    try {
      setState(87);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case T__0:
        case T__1:
          enterOuterAlt(_localctx, 1);
          {
            setState(81);
            boolean_();
          }
          break;
        case Numeral:
          enterOuterAlt(_localctx, 2);
          {
            setState(82);
            integer();
          }
          break;
        case Decimal:
          enterOuterAlt(_localctx, 3);
          {
            setState(83);
            real();
          }
          break;
        case Binary:
        case HexaDecimal:
          enterOuterAlt(_localctx, 4);
          {
            setState(84);
            bitvec();
          }
          break;
        case T__2:
          enterOuterAlt(_localctx, 5);
          {
            setState(85);
            float_();
          }
          break;
        case String:
          enterOuterAlt(_localctx, 6);
          {
            setState(86);
            string();
          }
          break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SymbolContext extends ParserRuleContext {
    public TerminalNode Simple() {
      return getToken(SmtlibParser.Simple, 0);
    }

    public TerminalNode Quoted() {
      return getToken(SmtlibParser.Quoted, 0);
    }

    public SymbolContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_symbol;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSymbol(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SymbolContext symbol() throws RecognitionException {
    SymbolContext _localctx = new SymbolContext(_ctx, getState());
    enterRule(_localctx, 14, RULE_symbol);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(89);
        _la = _input.LA(1);
        if (!(_la == Simple || _la == Quoted)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class KeywordContext extends ParserRuleContext {
    public TerminalNode Keyword() {
      return getToken(SmtlibParser.Keyword, 0);
    }

    public KeywordContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_keyword;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitKeyword(this);
      else return visitor.visitChildren(this);
    }
  }

  public final KeywordContext keyword() throws RecognitionException {
    KeywordContext _localctx = new KeywordContext(_ctx, getState());
    enterRule(_localctx, 16, RULE_keyword);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(91);
        match(Keyword);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortContext extends ParserRuleContext {
    public SortContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_sort;
    }

    public SortContext() {}

    public void copyFrom(SortContext ctx) {
      super.copyFrom(ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortStringContext extends SortContext {
    public SortStringContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortString(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortRegexContext extends SortContext {
    public SortRegexContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortRegex(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortFloatContext extends SortContext {
    public List<IntegerContext> integer() {
      return getRuleContexts(IntegerContext.class);
    }

    public IntegerContext integer(int i) {
      return getRuleContext(IntegerContext.class, i);
    }

    public SortFloatContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortFloat(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortBitvecContext extends SortContext {
    public IntegerContext integer() {
      return getRuleContext(IntegerContext.class, 0);
    }

    public SortBitvecContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortBitvec(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortRoundingModeContext extends SortContext {
    public SortRoundingModeContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortRoundingMode(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortBoolContext extends SortContext {
    public SortBoolContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortBool(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortIntContext extends SortContext {
    public SortIntContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortInt(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortRealContext extends SortContext {
    public SortRealContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortReal(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortArrayContext extends SortContext {
    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public SortArrayContext(SortContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortArray(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortContext sort() throws RecognitionException {
    SortContext _localctx = new SortContext(_ctx, getState());
    enterRule(_localctx, 18, RULE_sort);
    try {
      setState(124);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 2, _ctx)) {
        case 1:
          _localctx = new SortBoolContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(93);
            match(T__5);
          }
          break;
        case 2:
          _localctx = new SortIntContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(94);
            match(T__6);
          }
          break;
        case 3:
          _localctx = new SortRealContext(_localctx);
          enterOuterAlt(_localctx, 3);
          {
            setState(95);
            match(T__7);
          }
          break;
        case 4:
          _localctx = new SortStringContext(_localctx);
          enterOuterAlt(_localctx, 4);
          {
            setState(96);
            match(T__8);
          }
          break;
        case 5:
          _localctx = new SortRegexContext(_localctx);
          enterOuterAlt(_localctx, 5);
          {
            setState(97);
            match(T__9);
          }
          break;
        case 6:
          _localctx = new SortBitvecContext(_localctx);
          enterOuterAlt(_localctx, 6);
          {
            setState(98);
            match(T__2);
            setState(99);
            match(T__10);
            setState(100);
            match(T__11);
            setState(101);
            integer();
            setState(102);
            match(T__4);
          }
          break;
        case 7:
          _localctx = new SortRoundingModeContext(_localctx);
          enterOuterAlt(_localctx, 7);
          {
            setState(104);
            match(T__12);
          }
          break;
        case 8:
          _localctx = new SortFloatContext(_localctx);
          enterOuterAlt(_localctx, 8);
          {
            setState(116);
            _errHandler.sync(this);
            switch (_input.LA(1)) {
              case T__13:
                {
                  setState(105);
                  match(T__13);
                }
                break;
              case T__14:
                {
                  setState(106);
                  match(T__14);
                }
                break;
              case T__15:
                {
                  setState(107);
                  match(T__15);
                }
                break;
              case T__16:
                {
                  setState(108);
                  match(T__16);
                }
                break;
              case T__2:
                {
                  setState(109);
                  match(T__2);
                  setState(110);
                  match(T__10);
                  setState(111);
                  match(T__17);
                  setState(112);
                  integer();
                  setState(113);
                  integer();
                  setState(114);
                  match(T__4);
                }
                break;
              default:
                throw new NoViableAltException(this);
            }
          }
          break;
        case 9:
          _localctx = new SortArrayContext(_localctx);
          enterOuterAlt(_localctx, 9);
          {
            setState(118);
            match(T__2);
            setState(119);
            match(T__18);
            setState(120);
            sort();
            setState(121);
            sort();
            setState(122);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QuantifierContext extends ParserRuleContext {
    public QuantifierContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_quantifier;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitQuantifier(this);
      else return visitor.visitChildren(this);
    }
  }

  public final QuantifierContext quantifier() throws RecognitionException {
    QuantifierContext _localctx = new QuantifierContext(_ctx, getState());
    enterRule(_localctx, 20, RULE_quantifier);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(126);
        _la = _input.LA(1);
        if (!(_la == T__19 || _la == T__20)) {
          _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SortedVarContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public SortedVarContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_sortedVar;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSortedVar(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SortedVarContext sortedVar() throws RecognitionException {
    SortedVarContext _localctx = new SortedVarContext(_ctx, getState());
    enterRule(_localctx, 22, RULE_sortedVar);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(128);
        match(T__2);
        setState(129);
        symbol();
        setState(130);
        sort();
        setState(131);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class BindingContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public BindingContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_binding;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitBinding(this);
      else return visitor.visitChildren(this);
    }
  }

  public final BindingContext binding() throws RecognitionException {
    BindingContext _localctx = new BindingContext(_ctx, getState());
    enterRule(_localctx, 24, RULE_binding);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(133);
        match(T__2);
        setState(134);
        symbol();
        setState(135);
        expr();
        setState(136);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AttributeContext extends ParserRuleContext {
    public KeywordContext keyword() {
      return getRuleContext(KeywordContext.class, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public AttributeContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_attribute;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitAttribute(this);
      else return visitor.visitChildren(this);
    }
  }

  public final AttributeContext attribute() throws RecognitionException {
    AttributeContext _localctx = new AttributeContext(_ctx, getState());
    enterRule(_localctx, 26, RULE_attribute);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(138);
        keyword();
        setState(140);
        _errHandler.sync(this);
        _la = _input.LA(1);
        if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 17873661021126670L) != 0)) {
          {
            setState(139);
            expr();
          }
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ExprContext extends ParserRuleContext {
    public ExprContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_expr;
    }

    public ExprContext() {}

    public void copyFrom(ExprContext ctx) {
      super.copyFrom(ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AppContext extends ExprContext {
    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public AppContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitApp(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AnnotatedContext extends ExprContext {
    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public List<AttributeContext> attribute() {
      return getRuleContexts(AttributeContext.class);
    }

    public AttributeContext attribute(int i) {
      return getRuleContext(AttributeContext.class, i);
    }

    public AnnotatedContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitAnnotated(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AsContext extends ExprContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public AsContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitAs(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class QuantifiedContext extends ExprContext {
    public QuantifierContext quantifier() {
      return getRuleContext(QuantifierContext.class, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public List<SortedVarContext> sortedVar() {
      return getRuleContexts(SortedVarContext.class);
    }

    public SortedVarContext sortedVar(int i) {
      return getRuleContext(SortedVarContext.class, i);
    }

    public QuantifiedContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitQuantified(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class VarContext extends ExprContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public VarContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitVar(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ConstContext extends ExprContext {
    public LiteralContext literal() {
      return getRuleContext(LiteralContext.class, 0);
    }

    public ConstContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitConst(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class LetContext extends ExprContext {
    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public List<BindingContext> binding() {
      return getRuleContexts(BindingContext.class);
    }

    public BindingContext binding(int i) {
      return getRuleContext(BindingContext.class, i);
    }

    public LetContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitLet(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class IndexedContext extends ExprContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public List<IntegerContext> integer() {
      return getRuleContexts(IntegerContext.class);
    }

    public IntegerContext integer(int i) {
      return getRuleContext(IntegerContext.class, i);
    }

    public IndexedContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitIndexed(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ExprContext expr() throws RecognitionException {
    ExprContext _localctx = new ExprContext(_ctx, getState());
    enterRule(_localctx, 28, RULE_expr);
    int _la;
    try {
      setState(203);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 9, _ctx)) {
        case 1:
          _localctx = new ConstContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(142);
            literal();
          }
          break;
        case 2:
          _localctx = new VarContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(143);
            symbol();
          }
          break;
        case 3:
          _localctx = new IndexedContext(_localctx);
          enterOuterAlt(_localctx, 3);
          {
            setState(144);
            match(T__2);
            setState(145);
            match(T__10);
            setState(146);
            symbol();
            setState(148);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(147);
                  integer();
                }
              }
              setState(150);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == Numeral);
            setState(152);
            match(T__4);
          }
          break;
        case 4:
          _localctx = new AsContext(_localctx);
          enterOuterAlt(_localctx, 4);
          {
            setState(154);
            match(T__2);
            setState(155);
            match(T__21);
            setState(156);
            symbol();
            setState(157);
            sort();
            setState(158);
            match(T__4);
          }
          break;
        case 5:
          _localctx = new AnnotatedContext(_localctx);
          enterOuterAlt(_localctx, 5);
          {
            setState(160);
            match(T__2);
            setState(161);
            match(T__22);
            setState(162);
            expr();
            setState(164);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(163);
                  attribute();
                }
              }
              setState(166);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == Keyword);
            setState(168);
            match(T__4);
          }
          break;
        case 6:
          _localctx = new LetContext(_localctx);
          enterOuterAlt(_localctx, 6);
          {
            setState(170);
            match(T__2);
            setState(171);
            match(T__23);
            setState(172);
            match(T__2);
            setState(174);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(173);
                  binding();
                }
              }
              setState(176);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == T__2);
            setState(178);
            match(T__4);
            setState(179);
            expr();
            setState(180);
            match(T__4);
          }
          break;
        case 7:
          _localctx = new QuantifiedContext(_localctx);
          enterOuterAlt(_localctx, 7);
          {
            setState(182);
            match(T__2);
            setState(183);
            quantifier();
            setState(184);
            match(T__2);
            setState(186);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(185);
                  sortedVar();
                }
              }
              setState(188);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == T__2);
            setState(190);
            match(T__4);
            setState(191);
            expr();
            setState(192);
            match(T__4);
          }
          break;
        case 8:
          _localctx = new AppContext(_localctx);
          enterOuterAlt(_localctx, 8);
          {
            setState(194);
            match(T__2);
            setState(195);
            expr();
            setState(197);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(196);
                  expr();
                }
              }
              setState(199);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 17873661021126670L) != 0));
            setState(201);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetInfoContext extends ParserRuleContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public SetInfoContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_setInfo;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSetInfo(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SetInfoContext setInfo() throws RecognitionException {
    SetInfoContext _localctx = new SetInfoContext(_ctx, getState());
    enterRule(_localctx, 30, RULE_setInfo);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(205);
        match(T__2);
        setState(206);
        match(T__24);
        setState(207);
        attribute();
        setState(208);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetOptionContext extends ParserRuleContext {
    public AttributeContext attribute() {
      return getRuleContext(AttributeContext.class, 0);
    }

    public SetOptionContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_setOption;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSetOption(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SetOptionContext setOption() throws RecognitionException {
    SetOptionContext _localctx = new SetOptionContext(_ctx, getState());
    enterRule(_localctx, 32, RULE_setOption);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(210);
        match(T__2);
        setState(211);
        match(T__25);
        setState(212);
        attribute();
        setState(213);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SetLogicContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SetLogicContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_setLogic;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSetLogic(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SetLogicContext setLogic() throws RecognitionException {
    SetLogicContext _localctx = new SetLogicContext(_ctx, getState());
    enterRule(_localctx, 34, RULE_setLogic);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(215);
        match(T__2);
        setState(216);
        match(T__26);
        setState(217);
        symbol();
        setState(218);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DeclareContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public List<SortContext> sort() {
      return getRuleContexts(SortContext.class);
    }

    public SortContext sort(int i) {
      return getRuleContext(SortContext.class, i);
    }

    public DeclareContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_declare;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitDeclare(this);
      else return visitor.visitChildren(this);
    }
  }

  public final DeclareContext declare() throws RecognitionException {
    DeclareContext _localctx = new DeclareContext(_ctx, getState());
    enterRule(_localctx, 36, RULE_declare);
    int _la;
    try {
      setState(240);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 11, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(220);
            match(T__2);
            setState(221);
            match(T__27);
            setState(222);
            symbol();
            setState(223);
            sort();
            setState(224);
            match(T__4);
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(226);
            match(T__2);
            setState(227);
            match(T__28);
            setState(228);
            symbol();
            setState(229);
            match(T__2);
            setState(233);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 255944L) != 0)) {
              {
                {
                  setState(230);
                  sort();
                }
              }
              setState(235);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(236);
            match(T__4);
            setState(237);
            sort();
            setState(238);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class DefineContext extends ParserRuleContext {
    public SymbolContext symbol() {
      return getRuleContext(SymbolContext.class, 0);
    }

    public SortContext sort() {
      return getRuleContext(SortContext.class, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public List<SortedVarContext> sortedVar() {
      return getRuleContexts(SortedVarContext.class);
    }

    public SortedVarContext sortedVar(int i) {
      return getRuleContext(SortedVarContext.class, i);
    }

    public DefineContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_define;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitDefine(this);
      else return visitor.visitChildren(this);
    }
  }

  public final DefineContext define() throws RecognitionException {
    DefineContext _localctx = new DefineContext(_ctx, getState());
    enterRule(_localctx, 38, RULE_define);
    int _la;
    try {
      setState(264);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 13, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(242);
            match(T__2);
            setState(243);
            match(T__29);
            setState(244);
            symbol();
            setState(245);
            sort();
            setState(246);
            expr();
            setState(247);
            match(T__4);
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(249);
            match(T__2);
            setState(250);
            match(T__30);
            setState(251);
            symbol();
            setState(252);
            match(T__2);
            setState(256);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while (_la == T__2) {
              {
                {
                  setState(253);
                  sortedVar();
                }
              }
              setState(258);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(259);
            match(T__4);
            setState(260);
            sort();
            setState(261);
            expr();
            setState(262);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PushContext extends ParserRuleContext {
    public TerminalNode Numeral() {
      return getToken(SmtlibParser.Numeral, 0);
    }

    public PushContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_push;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitPush(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PushContext push() throws RecognitionException {
    PushContext _localctx = new PushContext(_ctx, getState());
    enterRule(_localctx, 40, RULE_push);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(266);
        match(T__2);
        setState(267);
        match(T__31);
        setState(268);
        match(Numeral);
        setState(269);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class PopContext extends ParserRuleContext {
    public TerminalNode Numeral() {
      return getToken(SmtlibParser.Numeral, 0);
    }

    public PopContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_pop;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitPop(this);
      else return visitor.visitChildren(this);
    }
  }

  public final PopContext pop() throws RecognitionException {
    PopContext _localctx = new PopContext(_ctx, getState());
    enterRule(_localctx, 42, RULE_pop);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(271);
        match(T__2);
        setState(272);
        match(T__32);
        setState(273);
        match(Numeral);
        setState(274);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class AssertContext extends ParserRuleContext {
    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public AssertContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_assert;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitAssert(this);
      else return visitor.visitChildren(this);
    }
  }

  public final AssertContext assert_() throws RecognitionException {
    AssertContext _localctx = new AssertContext(_ctx, getState());
    enterRule(_localctx, 44, RULE_assert);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(276);
        match(T__2);
        setState(277);
        match(T__33);
        setState(278);
        expr();
        setState(279);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetAssertionsContext extends ParserRuleContext {
    public GetAssertionsContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_getAssertions;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitGetAssertions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetAssertionsContext getAssertions() throws RecognitionException {
    GetAssertionsContext _localctx = new GetAssertionsContext(_ctx, getState());
    enterRule(_localctx, 46, RULE_getAssertions);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(281);
        match(T__2);
        setState(282);
        match(T__34);
        setState(283);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CheckContext extends ParserRuleContext {
    public CheckContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_check;
    }

    public CheckContext() {}

    public void copyFrom(CheckContext ctx) {
      super.copyFrom(ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CheckSatAssumingContext extends CheckContext {
    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public CheckSatAssumingContext(CheckContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitCheckSatAssuming(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CheckSatContext extends CheckContext {
    public CheckSatContext(CheckContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitCheckSat(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CheckContext check() throws RecognitionException {
    CheckContext _localctx = new CheckContext(_ctx, getState());
    enterRule(_localctx, 48, RULE_check);
    int _la;
    try {
      setState(299);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 15, _ctx)) {
        case 1:
          _localctx = new CheckSatContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(285);
            match(T__2);
            setState(286);
            match(T__35);
            setState(287);
            match(T__4);
          }
          break;
        case 2:
          _localctx = new CheckSatAssumingContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(288);
            match(T__2);
            setState(289);
            match(T__36);
            setState(290);
            match(T__2);
            setState(294);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 17873661021126670L) != 0)) {
              {
                {
                  setState(291);
                  expr();
                }
              }
              setState(296);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(297);
            match(T__4);
            setState(298);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetModelContext extends ParserRuleContext {
    public GetModelContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_getModel;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitGetModel(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetModelContext getModel() throws RecognitionException {
    GetModelContext _localctx = new GetModelContext(_ctx, getState());
    enterRule(_localctx, 50, RULE_getModel);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(301);
        match(T__2);
        setState(302);
        match(T__37);
        setState(303);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetCoreContext extends ParserRuleContext {
    public GetCoreContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_getCore;
    }

    public GetCoreContext() {}

    public void copyFrom(GetCoreContext ctx) {
      super.copyFrom(ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetUnsatCoreContext extends GetCoreContext {
    public GetUnsatCoreContext(GetCoreContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitGetUnsatCore(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetUnsatAssumptionsContext extends GetCoreContext {
    public GetUnsatAssumptionsContext(GetCoreContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitGetUnsatAssumptions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetCoreContext getCore() throws RecognitionException {
    GetCoreContext _localctx = new GetCoreContext(_ctx, getState());
    enterRule(_localctx, 52, RULE_getCore);
    try {
      setState(311);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 16, _ctx)) {
        case 1:
          _localctx = new GetUnsatCoreContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(305);
            match(T__2);
            setState(306);
            match(T__38);
            setState(307);
            match(T__4);
          }
          break;
        case 2:
          _localctx = new GetUnsatAssumptionsContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(308);
            match(T__2);
            setState(309);
            match(T__39);
            setState(310);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class GetValueContext extends ParserRuleContext {
    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public GetValueContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_getValue;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitGetValue(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GetValueContext getValue() throws RecognitionException {
    GetValueContext _localctx = new GetValueContext(_ctx, getState());
    enterRule(_localctx, 54, RULE_getValue);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(313);
        match(T__2);
        setState(314);
        match(T__40);
        setState(315);
        match(T__2);
        setState(317);
        _errHandler.sync(this);
        _la = _input.LA(1);
        do {
          {
            {
              setState(316);
              expr();
            }
          }
          setState(319);
          _errHandler.sync(this);
          _la = _input.LA(1);
        } while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 17873661021126670L) != 0));
        setState(321);
        match(T__4);
        setState(322);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResetContext extends ParserRuleContext {
    public ResetContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_reset;
    }

    public ResetContext() {}

    public void copyFrom(ResetContext ctx) {
      super.copyFrom(ctx);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResetSolverContext extends ResetContext {
    public ResetSolverContext(ResetContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitResetSolver(this);
      else return visitor.visitChildren(this);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ResetAssertionsContext extends ResetContext {
    public ResetAssertionsContext(ResetContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitResetAssertions(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ResetContext reset_() throws RecognitionException {
    ResetContext _localctx = new ResetContext(_ctx, getState());
    enterRule(_localctx, 56, RULE_reset);
    try {
      setState(330);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 18, _ctx)) {
        case 1:
          _localctx = new ResetSolverContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(324);
            match(T__2);
            setState(325);
            match(T__41);
            setState(326);
            match(T__4);
          }
          break;
        case 2:
          _localctx = new ResetAssertionsContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(327);
            match(T__2);
            setState(328);
            match(T__42);
            setState(329);
            match(T__4);
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class ExitContext extends ParserRuleContext {
    public ExitContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_exit;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitExit(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ExitContext exit() throws RecognitionException {
    ExitContext _localctx = new ExitContext(_ctx, getState());
    enterRule(_localctx, 58, RULE_exit);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(332);
        match(T__2);
        setState(333);
        match(T__43);
        setState(334);
        match(T__4);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class CommandContext extends ParserRuleContext {
    public SetInfoContext setInfo() {
      return getRuleContext(SetInfoContext.class, 0);
    }

    public SetOptionContext setOption() {
      return getRuleContext(SetOptionContext.class, 0);
    }

    public SetLogicContext setLogic() {
      return getRuleContext(SetLogicContext.class, 0);
    }

    public DeclareContext declare() {
      return getRuleContext(DeclareContext.class, 0);
    }

    public DefineContext define() {
      return getRuleContext(DefineContext.class, 0);
    }

    public PushContext push() {
      return getRuleContext(PushContext.class, 0);
    }

    public PopContext pop() {
      return getRuleContext(PopContext.class, 0);
    }

    public AssertContext assert_() {
      return getRuleContext(AssertContext.class, 0);
    }

    public GetAssertionsContext getAssertions() {
      return getRuleContext(GetAssertionsContext.class, 0);
    }

    public CheckContext check() {
      return getRuleContext(CheckContext.class, 0);
    }

    public GetModelContext getModel() {
      return getRuleContext(GetModelContext.class, 0);
    }

    public GetCoreContext getCore() {
      return getRuleContext(GetCoreContext.class, 0);
    }

    public GetValueContext getValue() {
      return getRuleContext(GetValueContext.class, 0);
    }

    public ResetContext reset_() {
      return getRuleContext(ResetContext.class, 0);
    }

    public ExitContext exit() {
      return getRuleContext(ExitContext.class, 0);
    }

    public CommandContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_command;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitCommand(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CommandContext command() throws RecognitionException {
    CommandContext _localctx = new CommandContext(_ctx, getState());
    enterRule(_localctx, 60, RULE_command);
    try {
      setState(351);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 19, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(336);
            setInfo();
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(337);
            setOption();
          }
          break;
        case 3:
          enterOuterAlt(_localctx, 3);
          {
            setState(338);
            setLogic();
          }
          break;
        case 4:
          enterOuterAlt(_localctx, 4);
          {
            setState(339);
            declare();
          }
          break;
        case 5:
          enterOuterAlt(_localctx, 5);
          {
            setState(340);
            define();
          }
          break;
        case 6:
          enterOuterAlt(_localctx, 6);
          {
            setState(341);
            push();
          }
          break;
        case 7:
          enterOuterAlt(_localctx, 7);
          {
            setState(342);
            pop();
          }
          break;
        case 8:
          enterOuterAlt(_localctx, 8);
          {
            setState(343);
            assert_();
          }
          break;
        case 9:
          enterOuterAlt(_localctx, 9);
          {
            setState(344);
            getAssertions();
          }
          break;
        case 10:
          enterOuterAlt(_localctx, 10);
          {
            setState(345);
            check();
          }
          break;
        case 11:
          enterOuterAlt(_localctx, 11);
          {
            setState(346);
            getModel();
          }
          break;
        case 12:
          enterOuterAlt(_localctx, 12);
          {
            setState(347);
            getCore();
          }
          break;
        case 13:
          enterOuterAlt(_localctx, 13);
          {
            setState(348);
            getValue();
          }
          break;
        case 14:
          enterOuterAlt(_localctx, 14);
          {
            setState(349);
            reset_();
          }
          break;
        case 15:
          enterOuterAlt(_localctx, 15);
          {
            setState(350);
            exit();
          }
          break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  @SuppressWarnings("CheckReturnValue")
  public static class SmtlibContext extends ParserRuleContext {
    public TerminalNode EOF() {
      return getToken(SmtlibParser.EOF, 0);
    }

    public List<CommandContext> command() {
      return getRuleContexts(CommandContext.class);
    }

    public CommandContext command(int i) {
      return getRuleContext(CommandContext.class, i);
    }

    public SmtlibContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_smtlib;
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof SmtlibVisitor)
        return ((SmtlibVisitor<? extends T>) visitor).visitSmtlib(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SmtlibContext smtlib() throws RecognitionException {
    SmtlibContext _localctx = new SmtlibContext(_ctx, getState());
    enterRule(_localctx, 62, RULE_smtlib);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(356);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == T__2) {
          {
            {
              setState(353);
              command();
            }
          }
          setState(358);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
        setState(359);
        match(EOF);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static final String _serializedATN =
      "\u0004\u00016\u016a\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"
          + "\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"
          + "\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"
          + "\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"
          + "\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"
          + "\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"
          + "\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002\u0015\u0007\u0015"
          + "\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017\u0002\u0018\u0007\u0018"
          + "\u0002\u0019\u0007\u0019\u0002\u001a\u0007\u001a\u0002\u001b\u0007\u001b"
          + "\u0002\u001c\u0007\u001c\u0002\u001d\u0007\u001d\u0002\u001e\u0007\u001e"
          + "\u0002\u001f\u0007\u001f\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001"
          + "\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002"
          + "\u0001\u0002\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004\u0001\u0005"
          + "\u0001\u0005\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"
          + "\u0001\u0006\u0003\u0006X\b\u0006\u0001\u0007\u0001\u0007\u0001\b\u0001"
          + "\b\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001"
          + "\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001"
          + "\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0003\tu\b\t\u0001\t\u0001"
          + "\t\u0001\t\u0001\t\u0001\t\u0001\t\u0003\t}\b\t\u0001\n\u0001\n\u0001"
          + "\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\f\u0001\f"
          + "\u0001\f\u0001\f\u0001\f\u0001\r\u0001\r\u0003\r\u008d\b\r\u0001\u000e"
          + "\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0004\u000e"
          + "\u0095\b\u000e\u000b\u000e\f\u000e\u0096\u0001\u000e\u0001\u000e\u0001"
          + "\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001"
          + "\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0004\u000e\u00a5\b\u000e\u000b"
          + "\u000e\f\u000e\u00a6\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001"
          + "\u000e\u0001\u000e\u0004\u000e\u00af\b\u000e\u000b\u000e\f\u000e\u00b0"
          + "\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e"
          + "\u0001\u000e\u0001\u000e\u0004\u000e\u00bb\b\u000e\u000b\u000e\f\u000e"
          + "\u00bc\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001"
          + "\u000e\u0001\u000e\u0004\u000e\u00c6\b\u000e\u000b\u000e\f\u000e\u00c7"
          + "\u0001\u000e\u0001\u000e\u0003\u000e\u00cc\b\u000e\u0001\u000f\u0001\u000f"
          + "\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u0010\u0001\u0010\u0001\u0010"
          + "\u0001\u0010\u0001\u0010\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0011"
          + "\u0001\u0011\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012"
          + "\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012"
          + "\u0005\u0012\u00e8\b\u0012\n\u0012\f\u0012\u00eb\t\u0012\u0001\u0012\u0001"
          + "\u0012\u0001\u0012\u0001\u0012\u0003\u0012\u00f1\b\u0012\u0001\u0013\u0001"
          + "\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001"
          + "\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0005\u0013\u00ff"
          + "\b\u0013\n\u0013\f\u0013\u0102\t\u0013\u0001\u0013\u0001\u0013\u0001\u0013"
          + "\u0001\u0013\u0001\u0013\u0003\u0013\u0109\b\u0013\u0001\u0014\u0001\u0014"
          + "\u0001\u0014\u0001\u0014\u0001\u0014\u0001\u0015\u0001\u0015\u0001\u0015"
          + "\u0001\u0015\u0001\u0015\u0001\u0016\u0001\u0016\u0001\u0016\u0001\u0016"
          + "\u0001\u0016\u0001\u0017\u0001\u0017\u0001\u0017\u0001\u0017\u0001\u0018"
          + "\u0001\u0018\u0001\u0018\u0001\u0018\u0001\u0018\u0001\u0018\u0001\u0018"
          + "\u0005\u0018\u0125\b\u0018\n\u0018\f\u0018\u0128\t\u0018\u0001\u0018\u0001"
          + "\u0018\u0003\u0018\u012c\b\u0018\u0001\u0019\u0001\u0019\u0001\u0019\u0001"
          + "\u0019\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001\u001a\u0001"
          + "\u001a\u0003\u001a\u0138\b\u001a\u0001\u001b\u0001\u001b\u0001\u001b\u0001"
          + "\u001b\u0004\u001b\u013e\b\u001b\u000b\u001b\f\u001b\u013f\u0001\u001b"
          + "\u0001\u001b\u0001\u001b\u0001\u001c\u0001\u001c\u0001\u001c\u0001\u001c"
          + "\u0001\u001c\u0001\u001c\u0003\u001c\u014b\b\u001c\u0001\u001d\u0001\u001d"
          + "\u0001\u001d\u0001\u001d\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e"
          + "\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e"
          + "\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0001\u001e\u0003\u001e"
          + "\u0160\b\u001e\u0001\u001f\u0005\u001f\u0163\b\u001f\n\u001f\f\u001f\u0166"
          + "\t\u001f\u0001\u001f\u0001\u001f\u0001\u001f\u0000\u0000 \u0000\u0002"
          + "\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0018\u001a\u001c\u001e"
          + " \"$&(*,.02468:<>\u0000\u0004\u0001\u0000\u0001\u0002\u0001\u0000/0\u0001"
          + "\u000045\u0001\u0000\u0014\u0015\u017f\u0000@\u0001\u0000\u0000\u0000"
          + "\u0002B\u0001\u0000\u0000\u0000\u0004D\u0001\u0000\u0000\u0000\u0006K"
          + "\u0001\u0000\u0000\u0000\bM\u0001\u0000\u0000\u0000\nO\u0001\u0000\u0000"
          + "\u0000\fW\u0001\u0000\u0000\u0000\u000eY\u0001\u0000\u0000\u0000\u0010"
          + "[\u0001\u0000\u0000\u0000\u0012|\u0001\u0000\u0000\u0000\u0014~\u0001"
          + "\u0000\u0000\u0000\u0016\u0080\u0001\u0000\u0000\u0000\u0018\u0085\u0001"
          + "\u0000\u0000\u0000\u001a\u008a\u0001\u0000\u0000\u0000\u001c\u00cb\u0001"
          + "\u0000\u0000\u0000\u001e\u00cd\u0001\u0000\u0000\u0000 \u00d2\u0001\u0000"
          + "\u0000\u0000\"\u00d7\u0001\u0000\u0000\u0000$\u00f0\u0001\u0000\u0000"
          + "\u0000&\u0108\u0001\u0000\u0000\u0000(\u010a\u0001\u0000\u0000\u0000*"
          + "\u010f\u0001\u0000\u0000\u0000,\u0114\u0001\u0000\u0000\u0000.\u0119\u0001"
          + "\u0000\u0000\u00000\u012b\u0001\u0000\u0000\u00002\u012d\u0001\u0000\u0000"
          + "\u00004\u0137\u0001\u0000\u0000\u00006\u0139\u0001\u0000\u0000\u00008"
          + "\u014a\u0001\u0000\u0000\u0000:\u014c\u0001\u0000\u0000\u0000<\u015f\u0001"
          + "\u0000\u0000\u0000>\u0164\u0001\u0000\u0000\u0000@A\u0007\u0000\u0000"
          + "\u0000A\u0001\u0001\u0000\u0000\u0000BC\u0007\u0001\u0000\u0000C\u0003"
          + "\u0001\u0000\u0000\u0000DE\u0005\u0003\u0000\u0000EF\u0005\u0004\u0000"
          + "\u0000FG\u0003\u0002\u0001\u0000GH\u0003\u0002\u0001\u0000HI\u0003\u0002"
          + "\u0001\u0000IJ\u0005\u0005\u0000\u0000J\u0005\u0001\u0000\u0000\u0000"
          + "KL\u00051\u0000\u0000L\u0007\u0001\u0000\u0000\u0000MN\u00052\u0000\u0000"
          + "N\t\u0001\u0000\u0000\u0000OP\u00053\u0000\u0000P\u000b\u0001\u0000\u0000"
          + "\u0000QX\u0003\u0000\u0000\u0000RX\u0003\u0006\u0003\u0000SX\u0003\b\u0004"
          + "\u0000TX\u0003\u0002\u0001\u0000UX\u0003\u0004\u0002\u0000VX\u0003\n\u0005"
          + "\u0000WQ\u0001\u0000\u0000\u0000WR\u0001\u0000\u0000\u0000WS\u0001\u0000"
          + "\u0000\u0000WT\u0001\u0000\u0000\u0000WU\u0001\u0000\u0000\u0000WV\u0001"
          + "\u0000\u0000\u0000X\r\u0001\u0000\u0000\u0000YZ\u0007\u0002\u0000\u0000"
          + "Z\u000f\u0001\u0000\u0000\u0000[\\\u00056\u0000\u0000\\\u0011\u0001\u0000"
          + "\u0000\u0000]}\u0005\u0006\u0000\u0000^}\u0005\u0007\u0000\u0000_}\u0005"
          + "\b\u0000\u0000`}\u0005\t\u0000\u0000a}\u0005\n\u0000\u0000bc\u0005\u0003"
          + "\u0000\u0000cd\u0005\u000b\u0000\u0000de\u0005\f\u0000\u0000ef\u0003\u0006"
          + "\u0003\u0000fg\u0005\u0005\u0000\u0000g}\u0001\u0000\u0000\u0000h}\u0005"
          + "\r\u0000\u0000iu\u0005\u000e\u0000\u0000ju\u0005\u000f\u0000\u0000ku\u0005"
          + "\u0010\u0000\u0000lu\u0005\u0011\u0000\u0000mn\u0005\u0003\u0000\u0000"
          + "no\u0005\u000b\u0000\u0000op\u0005\u0012\u0000\u0000pq\u0003\u0006\u0003"
          + "\u0000qr\u0003\u0006\u0003\u0000rs\u0005\u0005\u0000\u0000su\u0001\u0000"
          + "\u0000\u0000ti\u0001\u0000\u0000\u0000tj\u0001\u0000\u0000\u0000tk\u0001"
          + "\u0000\u0000\u0000tl\u0001\u0000\u0000\u0000tm\u0001\u0000\u0000\u0000"
          + "u}\u0001\u0000\u0000\u0000vw\u0005\u0003\u0000\u0000wx\u0005\u0013\u0000"
          + "\u0000xy\u0003\u0012\t\u0000yz\u0003\u0012\t\u0000z{\u0005\u0005\u0000"
          + "\u0000{}\u0001\u0000\u0000\u0000|]\u0001\u0000\u0000\u0000|^\u0001\u0000"
          + "\u0000\u0000|_\u0001\u0000\u0000\u0000|`\u0001\u0000\u0000\u0000|a\u0001"
          + "\u0000\u0000\u0000|b\u0001\u0000\u0000\u0000|h\u0001\u0000\u0000\u0000"
          + "|t\u0001\u0000\u0000\u0000|v\u0001\u0000\u0000\u0000}\u0013\u0001\u0000"
          + "\u0000\u0000~\u007f\u0007\u0003\u0000\u0000\u007f\u0015\u0001\u0000\u0000"
          + "\u0000\u0080\u0081\u0005\u0003\u0000\u0000\u0081\u0082\u0003\u000e\u0007"
          + "\u0000\u0082\u0083\u0003\u0012\t\u0000\u0083\u0084\u0005\u0005\u0000\u0000"
          + "\u0084\u0017\u0001\u0000\u0000\u0000\u0085\u0086\u0005\u0003\u0000\u0000"
          + "\u0086\u0087\u0003\u000e\u0007\u0000\u0087\u0088\u0003\u001c\u000e\u0000"
          + "\u0088\u0089\u0005\u0005\u0000\u0000\u0089\u0019\u0001\u0000\u0000\u0000"
          + "\u008a\u008c\u0003\u0010\b\u0000\u008b\u008d\u0003\u001c\u000e\u0000\u008c"
          + "\u008b\u0001\u0000\u0000\u0000\u008c\u008d\u0001\u0000\u0000\u0000\u008d"
          + "\u001b\u0001\u0000\u0000\u0000\u008e\u00cc\u0003\f\u0006\u0000\u008f\u00cc"
          + "\u0003\u000e\u0007\u0000\u0090\u0091\u0005\u0003\u0000\u0000\u0091\u0092"
          + "\u0005\u000b\u0000\u0000\u0092\u0094\u0003\u000e\u0007\u0000\u0093\u0095"
          + "\u0003\u0006\u0003\u0000\u0094\u0093\u0001\u0000\u0000\u0000\u0095\u0096"
          + "\u0001\u0000\u0000\u0000\u0096\u0094\u0001\u0000\u0000\u0000\u0096\u0097"
          + "\u0001\u0000\u0000\u0000\u0097\u0098\u0001\u0000\u0000\u0000\u0098\u0099"
          + "\u0005\u0005\u0000\u0000\u0099\u00cc\u0001\u0000\u0000\u0000\u009a\u009b"
          + "\u0005\u0003\u0000\u0000\u009b\u009c\u0005\u0016\u0000\u0000\u009c\u009d"
          + "\u0003\u000e\u0007\u0000\u009d\u009e\u0003\u0012\t\u0000\u009e\u009f\u0005"
          + "\u0005\u0000\u0000\u009f\u00cc\u0001\u0000\u0000\u0000\u00a0\u00a1\u0005"
          + "\u0003\u0000\u0000\u00a1\u00a2\u0005\u0017\u0000\u0000\u00a2\u00a4\u0003"
          + "\u001c\u000e\u0000\u00a3\u00a5\u0003\u001a\r\u0000\u00a4\u00a3\u0001\u0000"
          + "\u0000\u0000\u00a5\u00a6\u0001\u0000\u0000\u0000\u00a6\u00a4\u0001\u0000"
          + "\u0000\u0000\u00a6\u00a7\u0001\u0000\u0000\u0000\u00a7\u00a8\u0001\u0000"
          + "\u0000\u0000\u00a8\u00a9\u0005\u0005\u0000\u0000\u00a9\u00cc\u0001\u0000"
          + "\u0000\u0000\u00aa\u00ab\u0005\u0003\u0000\u0000\u00ab\u00ac\u0005\u0018"
          + "\u0000\u0000\u00ac\u00ae\u0005\u0003\u0000\u0000\u00ad\u00af\u0003\u0018"
          + "\f\u0000\u00ae\u00ad\u0001\u0000\u0000\u0000\u00af\u00b0\u0001\u0000\u0000"
          + "\u0000\u00b0\u00ae\u0001\u0000\u0000\u0000\u00b0\u00b1\u0001\u0000\u0000"
          + "\u0000\u00b1\u00b2\u0001\u0000\u0000\u0000\u00b2\u00b3\u0005\u0005\u0000"
          + "\u0000\u00b3\u00b4\u0003\u001c\u000e\u0000\u00b4\u00b5\u0005\u0005\u0000"
          + "\u0000\u00b5\u00cc\u0001\u0000\u0000\u0000\u00b6\u00b7\u0005\u0003\u0000"
          + "\u0000\u00b7\u00b8\u0003\u0014\n\u0000\u00b8\u00ba\u0005\u0003\u0000\u0000"
          + "\u00b9\u00bb\u0003\u0016\u000b\u0000\u00ba\u00b9\u0001\u0000\u0000\u0000"
          + "\u00bb\u00bc\u0001\u0000\u0000\u0000\u00bc\u00ba\u0001\u0000\u0000\u0000"
          + "\u00bc\u00bd\u0001\u0000\u0000\u0000\u00bd\u00be\u0001\u0000\u0000\u0000"
          + "\u00be\u00bf\u0005\u0005\u0000\u0000\u00bf\u00c0\u0003\u001c\u000e\u0000"
          + "\u00c0\u00c1\u0005\u0005\u0000\u0000\u00c1\u00cc\u0001\u0000\u0000\u0000"
          + "\u00c2\u00c3\u0005\u0003\u0000\u0000\u00c3\u00c5\u0003\u001c\u000e\u0000"
          + "\u00c4\u00c6\u0003\u001c\u000e\u0000\u00c5\u00c4\u0001\u0000\u0000\u0000"
          + "\u00c6\u00c7\u0001\u0000\u0000\u0000\u00c7\u00c5\u0001\u0000\u0000\u0000"
          + "\u00c7\u00c8\u0001\u0000\u0000\u0000\u00c8\u00c9\u0001\u0000\u0000\u0000"
          + "\u00c9\u00ca\u0005\u0005\u0000\u0000\u00ca\u00cc\u0001\u0000\u0000\u0000"
          + "\u00cb\u008e\u0001\u0000\u0000\u0000\u00cb\u008f\u0001\u0000\u0000\u0000"
          + "\u00cb\u0090\u0001\u0000\u0000\u0000\u00cb\u009a\u0001\u0000\u0000\u0000"
          + "\u00cb\u00a0\u0001\u0000\u0000\u0000\u00cb\u00aa\u0001\u0000\u0000\u0000"
          + "\u00cb\u00b6\u0001\u0000\u0000\u0000\u00cb\u00c2\u0001\u0000\u0000\u0000"
          + "\u00cc\u001d\u0001\u0000\u0000\u0000\u00cd\u00ce\u0005\u0003\u0000\u0000"
          + "\u00ce\u00cf\u0005\u0019\u0000\u0000\u00cf\u00d0\u0003\u001a\r\u0000\u00d0"
          + "\u00d1\u0005\u0005\u0000\u0000\u00d1\u001f\u0001\u0000\u0000\u0000\u00d2"
          + "\u00d3\u0005\u0003\u0000\u0000\u00d3\u00d4\u0005\u001a\u0000\u0000\u00d4"
          + "\u00d5\u0003\u001a\r\u0000\u00d5\u00d6\u0005\u0005\u0000\u0000\u00d6!"
          + "\u0001\u0000\u0000\u0000\u00d7\u00d8\u0005\u0003\u0000\u0000\u00d8\u00d9"
          + "\u0005\u001b\u0000\u0000\u00d9\u00da\u0003\u000e\u0007\u0000\u00da\u00db"
          + "\u0005\u0005\u0000\u0000\u00db#\u0001\u0000\u0000\u0000\u00dc\u00dd\u0005"
          + "\u0003\u0000\u0000\u00dd\u00de\u0005\u001c\u0000\u0000\u00de\u00df\u0003"
          + "\u000e\u0007\u0000\u00df\u00e0\u0003\u0012\t\u0000\u00e0\u00e1\u0005\u0005"
          + "\u0000\u0000\u00e1\u00f1\u0001\u0000\u0000\u0000\u00e2\u00e3\u0005\u0003"
          + "\u0000\u0000\u00e3\u00e4\u0005\u001d\u0000\u0000\u00e4\u00e5\u0003\u000e"
          + "\u0007\u0000\u00e5\u00e9\u0005\u0003\u0000\u0000\u00e6\u00e8\u0003\u0012"
          + "\t\u0000\u00e7\u00e6\u0001\u0000\u0000\u0000\u00e8\u00eb\u0001\u0000\u0000"
          + "\u0000\u00e9\u00e7\u0001\u0000\u0000\u0000\u00e9\u00ea\u0001\u0000\u0000"
          + "\u0000\u00ea\u00ec\u0001\u0000\u0000\u0000\u00eb\u00e9\u0001\u0000\u0000"
          + "\u0000\u00ec\u00ed\u0005\u0005\u0000\u0000\u00ed\u00ee\u0003\u0012\t\u0000"
          + "\u00ee\u00ef\u0005\u0005\u0000\u0000\u00ef\u00f1\u0001\u0000\u0000\u0000"
          + "\u00f0\u00dc\u0001\u0000\u0000\u0000\u00f0\u00e2\u0001\u0000\u0000\u0000"
          + "\u00f1%\u0001\u0000\u0000\u0000\u00f2\u00f3\u0005\u0003\u0000\u0000\u00f3"
          + "\u00f4\u0005\u001e\u0000\u0000\u00f4\u00f5\u0003\u000e\u0007\u0000\u00f5"
          + "\u00f6\u0003\u0012\t\u0000\u00f6\u00f7\u0003\u001c\u000e\u0000\u00f7\u00f8"
          + "\u0005\u0005\u0000\u0000\u00f8\u0109\u0001\u0000\u0000\u0000\u00f9\u00fa"
          + "\u0005\u0003\u0000\u0000\u00fa\u00fb\u0005\u001f\u0000\u0000\u00fb\u00fc"
          + "\u0003\u000e\u0007\u0000\u00fc\u0100\u0005\u0003\u0000\u0000\u00fd\u00ff"
          + "\u0003\u0016\u000b\u0000\u00fe\u00fd\u0001\u0000\u0000\u0000\u00ff\u0102"
          + "\u0001\u0000\u0000\u0000\u0100\u00fe\u0001\u0000\u0000\u0000\u0100\u0101"
          + "\u0001\u0000\u0000\u0000\u0101\u0103\u0001\u0000\u0000\u0000\u0102\u0100"
          + "\u0001\u0000\u0000\u0000\u0103\u0104\u0005\u0005\u0000\u0000\u0104\u0105"
          + "\u0003\u0012\t\u0000\u0105\u0106\u0003\u001c\u000e\u0000\u0106\u0107\u0005"
          + "\u0005\u0000\u0000\u0107\u0109\u0001\u0000\u0000\u0000\u0108\u00f2\u0001"
          + "\u0000\u0000\u0000\u0108\u00f9\u0001\u0000\u0000\u0000\u0109\'\u0001\u0000"
          + "\u0000\u0000\u010a\u010b\u0005\u0003\u0000\u0000\u010b\u010c\u0005 \u0000"
          + "\u0000\u010c\u010d\u00051\u0000\u0000\u010d\u010e\u0005\u0005\u0000\u0000"
          + "\u010e)\u0001\u0000\u0000\u0000\u010f\u0110\u0005\u0003\u0000\u0000\u0110"
          + "\u0111\u0005!\u0000\u0000\u0111\u0112\u00051\u0000\u0000\u0112\u0113\u0005"
          + "\u0005\u0000\u0000\u0113+\u0001\u0000\u0000\u0000\u0114\u0115\u0005\u0003"
          + "\u0000\u0000\u0115\u0116\u0005\"\u0000\u0000\u0116\u0117\u0003\u001c\u000e"
          + "\u0000\u0117\u0118\u0005\u0005\u0000\u0000\u0118-\u0001\u0000\u0000\u0000"
          + "\u0119\u011a\u0005\u0003\u0000\u0000\u011a\u011b\u0005#\u0000\u0000\u011b"
          + "\u011c\u0005\u0005\u0000\u0000\u011c/\u0001\u0000\u0000\u0000\u011d\u011e"
          + "\u0005\u0003\u0000\u0000\u011e\u011f\u0005$\u0000\u0000\u011f\u012c\u0005"
          + "\u0005\u0000\u0000\u0120\u0121\u0005\u0003\u0000\u0000\u0121\u0122\u0005"
          + "%\u0000\u0000\u0122\u0126\u0005\u0003\u0000\u0000\u0123\u0125\u0003\u001c"
          + "\u000e\u0000\u0124\u0123\u0001\u0000\u0000\u0000\u0125\u0128\u0001\u0000"
          + "\u0000\u0000\u0126\u0124\u0001\u0000\u0000\u0000\u0126\u0127\u0001\u0000"
          + "\u0000\u0000\u0127\u0129\u0001\u0000\u0000\u0000\u0128\u0126\u0001\u0000"
          + "\u0000\u0000\u0129\u012a\u0005\u0005\u0000\u0000\u012a\u012c\u0005\u0005"
          + "\u0000\u0000\u012b\u011d\u0001\u0000\u0000\u0000\u012b\u0120\u0001\u0000"
          + "\u0000\u0000\u012c1\u0001\u0000\u0000\u0000\u012d\u012e\u0005\u0003\u0000"
          + "\u0000\u012e\u012f\u0005&\u0000\u0000\u012f\u0130\u0005\u0005\u0000\u0000"
          + "\u01303\u0001\u0000\u0000\u0000\u0131\u0132\u0005\u0003\u0000\u0000\u0132"
          + "\u0133\u0005\'\u0000\u0000\u0133\u0138\u0005\u0005\u0000\u0000\u0134\u0135"
          + "\u0005\u0003\u0000\u0000\u0135\u0136\u0005(\u0000\u0000\u0136\u0138\u0005"
          + "\u0005\u0000\u0000\u0137\u0131\u0001\u0000\u0000\u0000\u0137\u0134\u0001"
          + "\u0000\u0000\u0000\u01385\u0001\u0000\u0000\u0000\u0139\u013a\u0005\u0003"
          + "\u0000\u0000\u013a\u013b\u0005)\u0000\u0000\u013b\u013d\u0005\u0003\u0000"
          + "\u0000\u013c\u013e\u0003\u001c\u000e\u0000\u013d\u013c\u0001\u0000\u0000"
          + "\u0000\u013e\u013f\u0001\u0000\u0000\u0000\u013f\u013d\u0001\u0000\u0000"
          + "\u0000\u013f\u0140\u0001\u0000\u0000\u0000\u0140\u0141\u0001\u0000\u0000"
          + "\u0000\u0141\u0142\u0005\u0005\u0000\u0000\u0142\u0143\u0005\u0005\u0000"
          + "\u0000\u01437\u0001\u0000\u0000\u0000\u0144\u0145\u0005\u0003\u0000\u0000"
          + "\u0145\u0146\u0005*\u0000\u0000\u0146\u014b\u0005\u0005\u0000\u0000\u0147"
          + "\u0148\u0005\u0003\u0000\u0000\u0148\u0149\u0005+\u0000\u0000\u0149\u014b"
          + "\u0005\u0005\u0000\u0000\u014a\u0144\u0001\u0000\u0000\u0000\u014a\u0147"
          + "\u0001\u0000\u0000\u0000\u014b9\u0001\u0000\u0000\u0000\u014c\u014d\u0005"
          + "\u0003\u0000\u0000\u014d\u014e\u0005,\u0000\u0000\u014e\u014f\u0005\u0005"
          + "\u0000\u0000\u014f;\u0001\u0000\u0000\u0000\u0150\u0160\u0003\u001e\u000f"
          + "\u0000\u0151\u0160\u0003 \u0010\u0000\u0152\u0160\u0003\"\u0011\u0000"
          + "\u0153\u0160\u0003$\u0012\u0000\u0154\u0160\u0003&\u0013\u0000\u0155\u0160"
          + "\u0003(\u0014\u0000\u0156\u0160\u0003*\u0015\u0000\u0157\u0160\u0003,"
          + "\u0016\u0000\u0158\u0160\u0003.\u0017\u0000\u0159\u0160\u00030\u0018\u0000"
          + "\u015a\u0160\u00032\u0019\u0000\u015b\u0160\u00034\u001a\u0000\u015c\u0160"
          + "\u00036\u001b\u0000\u015d\u0160\u00038\u001c\u0000\u015e\u0160\u0003:"
          + "\u001d\u0000\u015f\u0150\u0001\u0000\u0000\u0000\u015f\u0151\u0001\u0000"
          + "\u0000\u0000\u015f\u0152\u0001\u0000\u0000\u0000\u015f\u0153\u0001\u0000"
          + "\u0000\u0000\u015f\u0154\u0001\u0000\u0000\u0000\u015f\u0155\u0001\u0000"
          + "\u0000\u0000\u015f\u0156\u0001\u0000\u0000\u0000\u015f\u0157\u0001\u0000"
          + "\u0000\u0000\u015f\u0158\u0001\u0000\u0000\u0000\u015f\u0159\u0001\u0000"
          + "\u0000\u0000\u015f\u015a\u0001\u0000\u0000\u0000\u015f\u015b\u0001\u0000"
          + "\u0000\u0000\u015f\u015c\u0001\u0000\u0000\u0000\u015f\u015d\u0001\u0000"
          + "\u0000\u0000\u015f\u015e\u0001\u0000\u0000\u0000\u0160=\u0001\u0000\u0000"
          + "\u0000\u0161\u0163\u0003<\u001e\u0000\u0162\u0161\u0001\u0000\u0000\u0000"
          + "\u0163\u0166\u0001\u0000\u0000\u0000\u0164\u0162\u0001\u0000\u0000\u0000"
          + "\u0164\u0165\u0001\u0000\u0000\u0000\u0165\u0167\u0001\u0000\u0000\u0000"
          + "\u0166\u0164\u0001\u0000\u0000\u0000\u0167\u0168\u0005\u0000\u0000\u0001"
          + "\u0168?\u0001\u0000\u0000\u0000\u0015Wt|\u008c\u0096\u00a6\u00b0\u00bc"
          + "\u00c7\u00cb\u00e9\u00f0\u0100\u0108\u0126\u012b\u0137\u013f\u014a\u015f"
          + "\u0164";
  public static final ATN _ATN = new ATNDeserializer().deserialize(_serializedATN.toCharArray());

  static {
    _decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
    for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
      _decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
    }
  }
}
