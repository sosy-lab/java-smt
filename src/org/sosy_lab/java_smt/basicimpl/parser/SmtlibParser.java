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
public class SmtlibParser extends Parser {
  static {
    RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION);
  }

  protected static final DFA[] _decisionToDFA;
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
      Comment = 30,
      White = 31,
      Binary = 32,
      HexaDecimal = 33,
      Numeral = 34,
      Decimal = 35,
      Simple = 36,
      Quoted = 37,
      Keyword = 38;
  public static final int RULE_boolean = 0,
      RULE_bitvec = 1,
      RULE_float = 2,
      RULE_integer = 3,
      RULE_real = 4,
      RULE_literal = 5,
      RULE_symbol = 6,
      RULE_keyword = 7,
      RULE_sort = 8,
      RULE_quantifier = 9,
      RULE_sortedVar = 10,
      RULE_binding = 11,
      RULE_attribute = 12,
      RULE_expr = 13,
      RULE_setInfo = 14,
      RULE_setOption = 15,
      RULE_setLogic = 16,
      RULE_declare = 17,
      RULE_define = 18,
      RULE_assert = 19,
      RULE_command = 20,
      RULE_smtlib = 21;

  private static String[] makeRuleNames() {
    return new String[] {
      "boolean",
      "bitvec",
      "float",
      "integer",
      "real",
      "literal",
      "symbol",
      "keyword",
      "sort",
      "quantifier",
      "sortedVar",
      "binding",
      "attribute",
      "expr",
      "setInfo",
      "setOption",
      "setLogic",
      "declare",
      "define",
      "assert",
      "command",
      "smtlib"
    };
  }

  public static final String[] ruleNames = makeRuleNames();

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
      "'_'",
      "'BitVec'",
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
      "'assert'"
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
      "Comment",
      "White",
      "Binary",
      "HexaDecimal",
      "Numeral",
      "Decimal",
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
  @Deprecated public static final String[] tokenNames;

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
        setState(44);
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
        setState(46);
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
        setState(48);
        match(T__2);
        setState(49);
        match(T__3);
        setState(50);
        bitvec();
        setState(51);
        bitvec();
        setState(52);
        bitvec();
        setState(53);
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
        setState(55);
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
        setState(57);
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
    enterRule(_localctx, 10, RULE_literal);
    try {
      setState(64);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case T__0:
        case T__1:
          enterOuterAlt(_localctx, 1);
          {
            setState(59);
            boolean_();
          }
          break;
        case Numeral:
          enterOuterAlt(_localctx, 2);
          {
            setState(60);
            integer();
          }
          break;
        case Decimal:
          enterOuterAlt(_localctx, 3);
          {
            setState(61);
            real();
          }
          break;
        case Binary:
        case HexaDecimal:
          enterOuterAlt(_localctx, 4);
          {
            setState(62);
            bitvec();
          }
          break;
        case T__2:
          enterOuterAlt(_localctx, 5);
          {
            setState(63);
            float_();
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
    enterRule(_localctx, 12, RULE_symbol);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(66);
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
    enterRule(_localctx, 14, RULE_keyword);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(68);
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
    enterRule(_localctx, 16, RULE_sort);
    try {
      setState(98);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 2, _ctx)) {
        case 1:
          _localctx = new SortBoolContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(70);
            match(T__5);
          }
          break;
        case 2:
          _localctx = new SortIntContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(71);
            match(T__6);
          }
          break;
        case 3:
          _localctx = new SortRealContext(_localctx);
          enterOuterAlt(_localctx, 3);
          {
            setState(72);
            match(T__7);
          }
          break;
        case 4:
          _localctx = new SortBitvecContext(_localctx);
          enterOuterAlt(_localctx, 4);
          {
            setState(73);
            match(T__2);
            setState(74);
            match(T__8);
            setState(75);
            match(T__9);
            setState(76);
            integer();
            setState(77);
            match(T__4);
          }
          break;
        case 5:
          _localctx = new SortFloatContext(_localctx);
          enterOuterAlt(_localctx, 5);
          {
            setState(90);
            _errHandler.sync(this);
            switch (_input.LA(1)) {
              case T__10:
                {
                  setState(79);
                  match(T__10);
                }
                break;
              case T__11:
                {
                  setState(80);
                  match(T__11);
                }
                break;
              case T__12:
                {
                  setState(81);
                  match(T__12);
                }
                break;
              case T__13:
                {
                  setState(82);
                  match(T__13);
                }
                break;
              case T__2:
                {
                  setState(83);
                  match(T__2);
                  setState(84);
                  match(T__8);
                  setState(85);
                  match(T__14);
                  setState(86);
                  integer();
                  setState(87);
                  integer();
                  setState(88);
                  match(T__4);
                }
                break;
              default:
                throw new NoViableAltException(this);
            }
          }
          break;
        case 6:
          _localctx = new SortArrayContext(_localctx);
          enterOuterAlt(_localctx, 6);
          {
            setState(92);
            match(T__2);
            setState(93);
            match(T__15);
            setState(94);
            sort();
            setState(95);
            sort();
            setState(96);
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
    enterRule(_localctx, 18, RULE_quantifier);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(100);
        _la = _input.LA(1);
        if (!(_la == T__16 || _la == T__17)) {
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
    enterRule(_localctx, 20, RULE_sortedVar);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(102);
        match(T__2);
        setState(103);
        symbol();
        setState(104);
        sort();
        setState(105);
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
    enterRule(_localctx, 22, RULE_binding);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(107);
        match(T__2);
        setState(108);
        symbol();
        setState(109);
        expr();
        setState(110);
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
    enterRule(_localctx, 24, RULE_attribute);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(112);
        keyword();
        setState(114);
        _errHandler.sync(this);
        _la = _input.LA(1);
        if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 270582939662L) != 0)) {
          {
            setState(113);
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
    enterRule(_localctx, 26, RULE_expr);
    int _la;
    try {
      setState(177);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 9, _ctx)) {
        case 1:
          _localctx = new ConstContext(_localctx);
          enterOuterAlt(_localctx, 1);
          {
            setState(116);
            literal();
          }
          break;
        case 2:
          _localctx = new VarContext(_localctx);
          enterOuterAlt(_localctx, 2);
          {
            setState(117);
            symbol();
          }
          break;
        case 3:
          _localctx = new IndexedContext(_localctx);
          enterOuterAlt(_localctx, 3);
          {
            setState(118);
            match(T__2);
            setState(119);
            match(T__8);
            setState(120);
            symbol();
            setState(122);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(121);
                  integer();
                }
              }
              setState(124);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == Numeral);
            setState(126);
            match(T__4);
          }
          break;
        case 4:
          _localctx = new AsContext(_localctx);
          enterOuterAlt(_localctx, 4);
          {
            setState(128);
            match(T__2);
            setState(129);
            match(T__18);
            setState(130);
            symbol();
            setState(131);
            sort();
            setState(132);
            match(T__4);
          }
          break;
        case 5:
          _localctx = new AnnotatedContext(_localctx);
          enterOuterAlt(_localctx, 5);
          {
            setState(134);
            match(T__2);
            setState(135);
            match(T__19);
            setState(136);
            expr();
            setState(138);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(137);
                  attribute();
                }
              }
              setState(140);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == Keyword);
            setState(142);
            match(T__4);
          }
          break;
        case 6:
          _localctx = new LetContext(_localctx);
          enterOuterAlt(_localctx, 6);
          {
            setState(144);
            match(T__2);
            setState(145);
            match(T__20);
            setState(146);
            match(T__2);
            setState(148);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(147);
                  binding();
                }
              }
              setState(150);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == T__2);
            setState(152);
            match(T__4);
            setState(153);
            expr();
            setState(154);
            match(T__4);
          }
          break;
        case 7:
          _localctx = new QuantifiedContext(_localctx);
          enterOuterAlt(_localctx, 7);
          {
            setState(156);
            match(T__2);
            setState(157);
            quantifier();
            setState(158);
            match(T__2);
            setState(160);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(159);
                  sortedVar();
                }
              }
              setState(162);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while (_la == T__2);
            setState(164);
            match(T__4);
            setState(165);
            expr();
            setState(166);
            match(T__4);
          }
          break;
        case 8:
          _localctx = new AppContext(_localctx);
          enterOuterAlt(_localctx, 8);
          {
            setState(168);
            match(T__2);
            setState(169);
            expr();
            setState(171);
            _errHandler.sync(this);
            _la = _input.LA(1);
            do {
              {
                {
                  setState(170);
                  expr();
                }
              }
              setState(173);
              _errHandler.sync(this);
              _la = _input.LA(1);
            } while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 270582939662L) != 0));
            setState(175);
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
    enterRule(_localctx, 28, RULE_setInfo);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(179);
        match(T__2);
        setState(180);
        match(T__21);
        setState(181);
        attribute();
        setState(182);
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
    enterRule(_localctx, 30, RULE_setOption);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(184);
        match(T__2);
        setState(185);
        match(T__22);
        setState(186);
        attribute();
        setState(187);
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
    enterRule(_localctx, 32, RULE_setLogic);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(189);
        match(T__2);
        setState(190);
        match(T__23);
        setState(191);
        symbol();
        setState(192);
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
    enterRule(_localctx, 34, RULE_declare);
    int _la;
    try {
      setState(214);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 11, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(194);
            match(T__2);
            setState(195);
            match(T__24);
            setState(196);
            symbol();
            setState(197);
            sort();
            setState(198);
            match(T__4);
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(200);
            match(T__2);
            setState(201);
            match(T__25);
            setState(202);
            symbol();
            setState(203);
            match(T__2);
            setState(207);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 31176L) != 0)) {
              {
                {
                  setState(204);
                  sort();
                }
              }
              setState(209);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(210);
            match(T__4);
            setState(211);
            sort();
            setState(212);
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
    enterRule(_localctx, 36, RULE_define);
    int _la;
    try {
      setState(238);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 13, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(216);
            match(T__2);
            setState(217);
            match(T__26);
            setState(218);
            symbol();
            setState(219);
            sort();
            setState(220);
            expr();
            setState(221);
            match(T__4);
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(223);
            match(T__2);
            setState(224);
            match(T__27);
            setState(225);
            symbol();
            setState(226);
            match(T__2);
            setState(230);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while (_la == T__2) {
              {
                {
                  setState(227);
                  sortedVar();
                }
              }
              setState(232);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(233);
            match(T__4);
            setState(234);
            sort();
            setState(235);
            expr();
            setState(236);
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
    enterRule(_localctx, 38, RULE_assert);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(240);
        match(T__2);
        setState(241);
        match(T__28);
        setState(242);
        expr();
        setState(243);
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

    public AssertContext assert_() {
      return getRuleContext(AssertContext.class, 0);
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
    enterRule(_localctx, 40, RULE_command);
    try {
      setState(251);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 14, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
          {
            setState(245);
            setInfo();
          }
          break;
        case 2:
          enterOuterAlt(_localctx, 2);
          {
            setState(246);
            setOption();
          }
          break;
        case 3:
          enterOuterAlt(_localctx, 3);
          {
            setState(247);
            setLogic();
          }
          break;
        case 4:
          enterOuterAlt(_localctx, 4);
          {
            setState(248);
            declare();
          }
          break;
        case 5:
          enterOuterAlt(_localctx, 5);
          {
            setState(249);
            define();
          }
          break;
        case 6:
          enterOuterAlt(_localctx, 6);
          {
            setState(250);
            assert_();
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
    enterRule(_localctx, 42, RULE_smtlib);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(256);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == T__2) {
          {
            {
              setState(253);
              command();
            }
          }
          setState(258);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
        setState(259);
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
      "\u0004\u0001&\u0106\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"
          + "\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"
          + "\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"
          + "\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"
          + "\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"
          + "\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"
          + "\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002\u0015\u0007\u0015"
          + "\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0002\u0001\u0002"
          + "\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0003"
          + "\u0001\u0003\u0001\u0004\u0001\u0004\u0001\u0005\u0001\u0005\u0001\u0005"
          + "\u0001\u0005\u0001\u0005\u0003\u0005A\b\u0005\u0001\u0006\u0001\u0006"
          + "\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"
          + "\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"
          + "\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003\b[\b\b\u0001\b\u0001"
          + "\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003\bc\b\b\u0001\t\u0001\t\u0001"
          + "\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\u000b\u0001\u000b\u0001\u000b"
          + "\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0003\fs\b\f\u0001\r\u0001\r"
          + "\u0001\r\u0001\r\u0001\r\u0001\r\u0004\r{\b\r\u000b\r\f\r|\u0001\r\u0001"
          + "\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"
          + "\r\u0001\r\u0004\r\u008b\b\r\u000b\r\f\r\u008c\u0001\r\u0001\r\u0001\r"
          + "\u0001\r\u0001\r\u0001\r\u0004\r\u0095\b\r\u000b\r\f\r\u0096\u0001\r\u0001"
          + "\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0004\r\u00a1\b\r\u000b"
          + "\r\f\r\u00a2\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0004"
          + "\r\u00ac\b\r\u000b\r\f\r\u00ad\u0001\r\u0001\r\u0003\r\u00b2\b\r\u0001"
          + "\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000f\u0001"
          + "\u000f\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u0010\u0001\u0010\u0001"
          + "\u0010\u0001\u0010\u0001\u0010\u0001\u0011\u0001\u0011\u0001\u0011\u0001"
          + "\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0001"
          + "\u0011\u0001\u0011\u0005\u0011\u00ce\b\u0011\n\u0011\f\u0011\u00d1\t\u0011"
          + "\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0003\u0011\u00d7\b\u0011"
          + "\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012"
          + "\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012"
          + "\u0005\u0012\u00e5\b\u0012\n\u0012\f\u0012\u00e8\t\u0012\u0001\u0012\u0001"
          + "\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0003\u0012\u00ef\b\u0012\u0001"
          + "\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0013\u0001\u0014\u0001"
          + "\u0014\u0001\u0014\u0001\u0014\u0001\u0014\u0001\u0014\u0003\u0014\u00fc"
          + "\b\u0014\u0001\u0015\u0005\u0015\u00ff\b\u0015\n\u0015\f\u0015\u0102\t"
          + "\u0015\u0001\u0015\u0001\u0015\u0001\u0015\u0000\u0000\u0016\u0000\u0002"
          + "\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0018\u001a\u001c\u001e"
          + " \"$&(*\u0000\u0004\u0001\u0000\u0001\u0002\u0001\u0000 !\u0001\u0000"
          + "$%\u0001\u0000\u0011\u0012\u0113\u0000,\u0001\u0000\u0000\u0000\u0002"
          + ".\u0001\u0000\u0000\u0000\u00040\u0001\u0000\u0000\u0000\u00067\u0001"
          + "\u0000\u0000\u0000\b9\u0001\u0000\u0000\u0000\n@\u0001\u0000\u0000\u0000"
          + "\fB\u0001\u0000\u0000\u0000\u000eD\u0001\u0000\u0000\u0000\u0010b\u0001"
          + "\u0000\u0000\u0000\u0012d\u0001\u0000\u0000\u0000\u0014f\u0001\u0000\u0000"
          + "\u0000\u0016k\u0001\u0000\u0000\u0000\u0018p\u0001\u0000\u0000\u0000\u001a"
          + "\u00b1\u0001\u0000\u0000\u0000\u001c\u00b3\u0001\u0000\u0000\u0000\u001e"
          + "\u00b8\u0001\u0000\u0000\u0000 \u00bd\u0001\u0000\u0000\u0000\"\u00d6"
          + "\u0001\u0000\u0000\u0000$\u00ee\u0001\u0000\u0000\u0000&\u00f0\u0001\u0000"
          + "\u0000\u0000(\u00fb\u0001\u0000\u0000\u0000*\u0100\u0001\u0000\u0000\u0000"
          + ",-\u0007\u0000\u0000\u0000-\u0001\u0001\u0000\u0000\u0000./\u0007\u0001"
          + "\u0000\u0000/\u0003\u0001\u0000\u0000\u000001\u0005\u0003\u0000\u0000"
          + "12\u0005\u0004\u0000\u000023\u0003\u0002\u0001\u000034\u0003\u0002\u0001"
          + "\u000045\u0003\u0002\u0001\u000056\u0005\u0005\u0000\u00006\u0005\u0001"
          + "\u0000\u0000\u000078\u0005\"\u0000\u00008\u0007\u0001\u0000\u0000\u0000"
          + "9:\u0005#\u0000\u0000:\t\u0001\u0000\u0000\u0000;A\u0003\u0000\u0000\u0000"
          + "<A\u0003\u0006\u0003\u0000=A\u0003\b\u0004\u0000>A\u0003\u0002\u0001\u0000"
          + "?A\u0003\u0004\u0002\u0000@;\u0001\u0000\u0000\u0000@<\u0001\u0000\u0000"
          + "\u0000@=\u0001\u0000\u0000\u0000@>\u0001\u0000\u0000\u0000@?\u0001\u0000"
          + "\u0000\u0000A\u000b\u0001\u0000\u0000\u0000BC\u0007\u0002\u0000\u0000"
          + "C\r\u0001\u0000\u0000\u0000DE\u0005&\u0000\u0000E\u000f\u0001\u0000\u0000"
          + "\u0000Fc\u0005\u0006\u0000\u0000Gc\u0005\u0007\u0000\u0000Hc\u0005\b\u0000"
          + "\u0000IJ\u0005\u0003\u0000\u0000JK\u0005\t\u0000\u0000KL\u0005\n\u0000"
          + "\u0000LM\u0003\u0006\u0003\u0000MN\u0005\u0005\u0000\u0000Nc\u0001\u0000"
          + "\u0000\u0000O[\u0005\u000b\u0000\u0000P[\u0005\f\u0000\u0000Q[\u0005\r"
          + "\u0000\u0000R[\u0005\u000e\u0000\u0000ST\u0005\u0003\u0000\u0000TU\u0005"
          + "\t\u0000\u0000UV\u0005\u000f\u0000\u0000VW\u0003\u0006\u0003\u0000WX\u0003"
          + "\u0006\u0003\u0000XY\u0005\u0005\u0000\u0000Y[\u0001\u0000\u0000\u0000"
          + "ZO\u0001\u0000\u0000\u0000ZP\u0001\u0000\u0000\u0000ZQ\u0001\u0000\u0000"
          + "\u0000ZR\u0001\u0000\u0000\u0000ZS\u0001\u0000\u0000\u0000[c\u0001\u0000"
          + "\u0000\u0000\\]\u0005\u0003\u0000\u0000]^\u0005\u0010\u0000\u0000^_\u0003"
          + "\u0010\b\u0000_`\u0003\u0010\b\u0000`a\u0005\u0005\u0000\u0000ac\u0001"
          + "\u0000\u0000\u0000bF\u0001\u0000\u0000\u0000bG\u0001\u0000\u0000\u0000"
          + "bH\u0001\u0000\u0000\u0000bI\u0001\u0000\u0000\u0000bZ\u0001\u0000\u0000"
          + "\u0000b\\\u0001\u0000\u0000\u0000c\u0011\u0001\u0000\u0000\u0000de\u0007"
          + "\u0003\u0000\u0000e\u0013\u0001\u0000\u0000\u0000fg\u0005\u0003\u0000"
          + "\u0000gh\u0003\f\u0006\u0000hi\u0003\u0010\b\u0000ij\u0005\u0005\u0000"
          + "\u0000j\u0015\u0001\u0000\u0000\u0000kl\u0005\u0003\u0000\u0000lm\u0003"
          + "\f\u0006\u0000mn\u0003\u001a\r\u0000no\u0005\u0005\u0000\u0000o\u0017"
          + "\u0001\u0000\u0000\u0000pr\u0003\u000e\u0007\u0000qs\u0003\u001a\r\u0000"
          + "rq\u0001\u0000\u0000\u0000rs\u0001\u0000\u0000\u0000s\u0019\u0001\u0000"
          + "\u0000\u0000t\u00b2\u0003\n\u0005\u0000u\u00b2\u0003\f\u0006\u0000vw\u0005"
          + "\u0003\u0000\u0000wx\u0005\t\u0000\u0000xz\u0003\f\u0006\u0000y{\u0003"
          + "\u0006\u0003\u0000zy\u0001\u0000\u0000\u0000{|\u0001\u0000\u0000\u0000"
          + "|z\u0001\u0000\u0000\u0000|}\u0001\u0000\u0000\u0000}~\u0001\u0000\u0000"
          + "\u0000~\u007f\u0005\u0005\u0000\u0000\u007f\u00b2\u0001\u0000\u0000\u0000"
          + "\u0080\u0081\u0005\u0003\u0000\u0000\u0081\u0082\u0005\u0013\u0000\u0000"
          + "\u0082\u0083\u0003\f\u0006\u0000\u0083\u0084\u0003\u0010\b\u0000\u0084"
          + "\u0085\u0005\u0005\u0000\u0000\u0085\u00b2\u0001\u0000\u0000\u0000\u0086"
          + "\u0087\u0005\u0003\u0000\u0000\u0087\u0088\u0005\u0014\u0000\u0000\u0088"
          + "\u008a\u0003\u001a\r\u0000\u0089\u008b\u0003\u0018\f\u0000\u008a\u0089"
          + "\u0001\u0000\u0000\u0000\u008b\u008c\u0001\u0000\u0000\u0000\u008c\u008a"
          + "\u0001\u0000\u0000\u0000\u008c\u008d\u0001\u0000\u0000\u0000\u008d\u008e"
          + "\u0001\u0000\u0000\u0000\u008e\u008f\u0005\u0005\u0000\u0000\u008f\u00b2"
          + "\u0001\u0000\u0000\u0000\u0090\u0091\u0005\u0003\u0000\u0000\u0091\u0092"
          + "\u0005\u0015\u0000\u0000\u0092\u0094\u0005\u0003\u0000\u0000\u0093\u0095"
          + "\u0003\u0016\u000b\u0000\u0094\u0093\u0001\u0000\u0000\u0000\u0095\u0096"
          + "\u0001\u0000\u0000\u0000\u0096\u0094\u0001\u0000\u0000\u0000\u0096\u0097"
          + "\u0001\u0000\u0000\u0000\u0097\u0098\u0001\u0000\u0000\u0000\u0098\u0099"
          + "\u0005\u0005\u0000\u0000\u0099\u009a\u0003\u001a\r\u0000\u009a\u009b\u0005"
          + "\u0005\u0000\u0000\u009b\u00b2\u0001\u0000\u0000\u0000\u009c\u009d\u0005"
          + "\u0003\u0000\u0000\u009d\u009e\u0003\u0012\t\u0000\u009e\u00a0\u0005\u0003"
          + "\u0000\u0000\u009f\u00a1\u0003\u0014\n\u0000\u00a0\u009f\u0001\u0000\u0000"
          + "\u0000\u00a1\u00a2\u0001\u0000\u0000\u0000\u00a2\u00a0\u0001\u0000\u0000"
          + "\u0000\u00a2\u00a3\u0001\u0000\u0000\u0000\u00a3\u00a4\u0001\u0000\u0000"
          + "\u0000\u00a4\u00a5\u0005\u0005\u0000\u0000\u00a5\u00a6\u0003\u001a\r\u0000"
          + "\u00a6\u00a7\u0005\u0005\u0000\u0000\u00a7\u00b2\u0001\u0000\u0000\u0000"
          + "\u00a8\u00a9\u0005\u0003\u0000\u0000\u00a9\u00ab\u0003\u001a\r\u0000\u00aa"
          + "\u00ac\u0003\u001a\r\u0000\u00ab\u00aa\u0001\u0000\u0000\u0000\u00ac\u00ad"
          + "\u0001\u0000\u0000\u0000\u00ad\u00ab\u0001\u0000\u0000\u0000\u00ad\u00ae"
          + "\u0001\u0000\u0000\u0000\u00ae\u00af\u0001\u0000\u0000\u0000\u00af\u00b0"
          + "\u0005\u0005\u0000\u0000\u00b0\u00b2\u0001\u0000\u0000\u0000\u00b1t\u0001"
          + "\u0000\u0000\u0000\u00b1u\u0001\u0000\u0000\u0000\u00b1v\u0001\u0000\u0000"
          + "\u0000\u00b1\u0080\u0001\u0000\u0000\u0000\u00b1\u0086\u0001\u0000\u0000"
          + "\u0000\u00b1\u0090\u0001\u0000\u0000\u0000\u00b1\u009c\u0001\u0000\u0000"
          + "\u0000\u00b1\u00a8\u0001\u0000\u0000\u0000\u00b2\u001b\u0001\u0000\u0000"
          + "\u0000\u00b3\u00b4\u0005\u0003\u0000\u0000\u00b4\u00b5\u0005\u0016\u0000"
          + "\u0000\u00b5\u00b6\u0003\u0018\f\u0000\u00b6\u00b7\u0005\u0005\u0000\u0000"
          + "\u00b7\u001d\u0001\u0000\u0000\u0000\u00b8\u00b9\u0005\u0003\u0000\u0000"
          + "\u00b9\u00ba\u0005\u0017\u0000\u0000\u00ba\u00bb\u0003\u0018\f\u0000\u00bb"
          + "\u00bc\u0005\u0005\u0000\u0000\u00bc\u001f\u0001\u0000\u0000\u0000\u00bd"
          + "\u00be\u0005\u0003\u0000\u0000\u00be\u00bf\u0005\u0018\u0000\u0000\u00bf"
          + "\u00c0\u0003\f\u0006\u0000\u00c0\u00c1\u0005\u0005\u0000\u0000\u00c1!"
          + "\u0001\u0000\u0000\u0000\u00c2\u00c3\u0005\u0003\u0000\u0000\u00c3\u00c4"
          + "\u0005\u0019\u0000\u0000\u00c4\u00c5\u0003\f\u0006\u0000\u00c5\u00c6\u0003"
          + "\u0010\b\u0000\u00c6\u00c7\u0005\u0005\u0000\u0000\u00c7\u00d7\u0001\u0000"
          + "\u0000\u0000\u00c8\u00c9\u0005\u0003\u0000\u0000\u00c9\u00ca\u0005\u001a"
          + "\u0000\u0000\u00ca\u00cb\u0003\f\u0006\u0000\u00cb\u00cf\u0005\u0003\u0000"
          + "\u0000\u00cc\u00ce\u0003\u0010\b\u0000\u00cd\u00cc\u0001\u0000\u0000\u0000"
          + "\u00ce\u00d1\u0001\u0000\u0000\u0000\u00cf\u00cd\u0001\u0000\u0000\u0000"
          + "\u00cf\u00d0\u0001\u0000\u0000\u0000\u00d0\u00d2\u0001\u0000\u0000\u0000"
          + "\u00d1\u00cf\u0001\u0000\u0000\u0000\u00d2\u00d3\u0005\u0005\u0000\u0000"
          + "\u00d3\u00d4\u0003\u0010\b\u0000\u00d4\u00d5\u0005\u0005\u0000\u0000\u00d5"
          + "\u00d7\u0001\u0000\u0000\u0000\u00d6\u00c2\u0001\u0000\u0000\u0000\u00d6"
          + "\u00c8\u0001\u0000\u0000\u0000\u00d7#\u0001\u0000\u0000\u0000\u00d8\u00d9"
          + "\u0005\u0003\u0000\u0000\u00d9\u00da\u0005\u001b\u0000\u0000\u00da\u00db"
          + "\u0003\f\u0006\u0000\u00db\u00dc\u0003\u0010\b\u0000\u00dc\u00dd\u0003"
          + "\u001a\r\u0000\u00dd\u00de\u0005\u0005\u0000\u0000\u00de\u00ef\u0001\u0000"
          + "\u0000\u0000\u00df\u00e0\u0005\u0003\u0000\u0000\u00e0\u00e1\u0005\u001c"
          + "\u0000\u0000\u00e1\u00e2\u0003\f\u0006\u0000\u00e2\u00e6\u0005\u0003\u0000"
          + "\u0000\u00e3\u00e5\u0003\u0014\n\u0000\u00e4\u00e3\u0001\u0000\u0000\u0000"
          + "\u00e5\u00e8\u0001\u0000\u0000\u0000\u00e6\u00e4\u0001\u0000\u0000\u0000"
          + "\u00e6\u00e7\u0001\u0000\u0000\u0000\u00e7\u00e9\u0001\u0000\u0000\u0000"
          + "\u00e8\u00e6\u0001\u0000\u0000\u0000\u00e9\u00ea\u0005\u0005\u0000\u0000"
          + "\u00ea\u00eb\u0003\u0010\b\u0000\u00eb\u00ec\u0003\u001a\r\u0000\u00ec"
          + "\u00ed\u0005\u0005\u0000\u0000\u00ed\u00ef\u0001\u0000\u0000\u0000\u00ee"
          + "\u00d8\u0001\u0000\u0000\u0000\u00ee\u00df\u0001\u0000\u0000\u0000\u00ef"
          + "%\u0001\u0000\u0000\u0000\u00f0\u00f1\u0005\u0003\u0000\u0000\u00f1\u00f2"
          + "\u0005\u001d\u0000\u0000\u00f2\u00f3\u0003\u001a\r\u0000\u00f3\u00f4\u0005"
          + "\u0005\u0000\u0000\u00f4\'\u0001\u0000\u0000\u0000\u00f5\u00fc\u0003\u001c"
          + "\u000e\u0000\u00f6\u00fc\u0003\u001e\u000f\u0000\u00f7\u00fc\u0003 \u0010"
          + "\u0000\u00f8\u00fc\u0003\"\u0011\u0000\u00f9\u00fc\u0003$\u0012\u0000"
          + "\u00fa\u00fc\u0003&\u0013\u0000\u00fb\u00f5\u0001\u0000\u0000\u0000\u00fb"
          + "\u00f6\u0001\u0000\u0000\u0000\u00fb\u00f7\u0001\u0000\u0000\u0000\u00fb"
          + "\u00f8\u0001\u0000\u0000\u0000\u00fb\u00f9\u0001\u0000\u0000\u0000\u00fb"
          + "\u00fa\u0001\u0000\u0000\u0000\u00fc)\u0001\u0000\u0000\u0000\u00fd\u00ff"
          + "\u0003(\u0014\u0000\u00fe\u00fd\u0001\u0000\u0000\u0000\u00ff\u0102\u0001"
          + "\u0000\u0000\u0000\u0100\u00fe\u0001\u0000\u0000\u0000\u0100\u0101\u0001"
          + "\u0000\u0000\u0000\u0101\u0103\u0001\u0000\u0000\u0000\u0102\u0100\u0001"
          + "\u0000\u0000\u0000\u0103\u0104\u0005\u0000\u0000\u0001\u0104+\u0001\u0000"
          + "\u0000\u0000\u0010@Zbr|\u008c\u0096\u00a2\u00ad\u00b1\u00cf\u00d6\u00e6"
          + "\u00ee\u00fb\u0100";
  public static final ATN _ATN = new ATNDeserializer().deserialize(_serializedATN.toCharArray());

  static {
    _decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
    for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
      _decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
    }
  }
}
