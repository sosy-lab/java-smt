// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.basicimpl.Tokenizer;

/** LeanSMT-specific SMT-LIB parser for declarations + asserted formulas. */
final class LeanSmtParser {

  private enum SymbolKind {
    VARIABLE,
    FUNCTION
  }

  private static final class SymbolDecl {
    private final SymbolKind kind;
    private final LeanSmtType variableType;
    private final LeanSmtFunctionDecl functionDecl;

    private SymbolDecl(SymbolKind pKind, LeanSmtType pVariableType, LeanSmtFunctionDecl pFunctionDecl) {
      kind = pKind;
      variableType = pVariableType;
      functionDecl = pFunctionDecl;
    }

    static SymbolDecl variable(LeanSmtType type) {
      return new SymbolDecl(SymbolKind.VARIABLE, type, null);
    }

    static SymbolDecl function(LeanSmtFunctionDecl decl) {
      return new SymbolDecl(SymbolKind.FUNCTION, null, decl);
    }
  }

  private static final class Term {
    private final long handle;
    private final LeanSmtType type;

    private Term(long pHandle, LeanSmtType pType) {
      handle = pHandle;
      type = pType;
    }
  }

  private static final class ParamDecl {
    private final String name;
    private final LeanSmtType type;

    private ParamDecl(String pName, LeanSmtType pType) {
      name = pName;
      type = pType;
    }
  }

  private static final class MacroDef {
    private final ImmutableList<ParamDecl> params;
    private final LeanSmtType returnType;
    private final SExpr body;

    private MacroDef(ImmutableList<ParamDecl> pParams, LeanSmtType pReturnType, SExpr pBody) {
      params = pParams;
      returnType = pReturnType;
      body = pBody;
    }
  }

  private static final class SExpr {
    private final @Nullable String atom;
    private final @Nullable List<SExpr> list;

    private SExpr(@Nullable String pAtom, @Nullable List<SExpr> pList) {
      atom = pAtom;
      list = pList;
    }

    static SExpr atom(String value) {
      return new SExpr(value, null);
    }

    static SExpr list(List<SExpr> values) {
      return new SExpr(null, values);
    }

    boolean isAtom() {
      return atom != null;
    }

    String getAtom() {
      Preconditions.checkState(atom != null, "Expected atom expression");
      return atom;
    }

    List<SExpr> getList() {
      Preconditions.checkState(list != null, "Expected list expression");
      return list;
    }
  }

  private final LeanSmtFormulaCreator creator;
  private final Map<String, SymbolDecl> symbols = new LinkedHashMap<>();
  private final Map<String, Term> constantDefinitions = new LinkedHashMap<>();
  private final Map<String, MacroDef> macroDefinitions = new LinkedHashMap<>();
  private final Set<String> unsupportedSymbols = new HashSet<>();

  LeanSmtParser(LeanSmtFormulaCreator pCreator) {
    creator = pCreator;
    for (Map.Entry<String, LeanSmtType> e : creator.getDeclaredVariableTypes().entrySet()) {
      symbols.put(e.getKey(), SymbolDecl.variable(e.getValue()));
    }
    for (LeanSmtFunctionDecl decl : creator.getKnownUfDeclarations()) {
      symbols.put(decl.getName(), SymbolDecl.function(decl));
    }
  }

  long parse(String smtQuery) {
    List<String> commands = Tokenizer.tokenize(smtQuery);
    if (commands.isEmpty()) {
      throw new IllegalArgumentException("Expected at least one SMT-LIB command");
    }

    List<Term> assertions = new ArrayList<>();
    for (String command : commands) {
      SExpr expr = parseSExpr(command);
      List<SExpr> items = expr.getList();
      if (items.isEmpty() || !items.get(0).isAtom()) {
        throw new IllegalArgumentException("Malformed SMT-LIB command: " + command);
      }
      String head = items.get(0).getAtom();
      switch (head) {
        case "declare-const":
          parseDeclareConst(items);
          break;
        case "declare-fun":
          parseDeclareFun(items);
          break;
        case "define-const":
          parseDefineConst(items);
          break;
        case "define-fun":
          parseDefineFun(items);
          break;
        case "assert":
          parseAssert(items, assertions);
          break;
        default:
          throw new IllegalArgumentException(
              "Unsupported SMT-LIB command for LeanSMT parser: " + head);
      }
    }

    if (assertions.isEmpty()) {
      throw new IllegalArgumentException("Expected at least one assertion in SMT-LIB input");
    }

    Term result = assertions.get(0);
    for (int i = 1; i < assertions.size(); i++) {
      result =
          new Term(
              creator.makeBinary(
                  "and",
                  FunctionDeclarationKind.AND,
                  FormulaType.BooleanType,
                  result.handle,
                  assertions.get(i).handle,
                  LeanSmtNativeApi::mkAnd),
              LeanSmtType.BOOL);
    }
    return result.handle;
  }

  private void parseDeclareConst(List<SExpr> items) {
    if (items.size() != 3 || !items.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed declare-const command");
    }
    String name = decodeIdentifier(items.get(1).getAtom());
    @Nullable LeanSmtType type = parseSortOrNull(items.get(2));
    if (type == null) {
      unsupportedSymbols.add(name);
      return;
    }
    declareSymbol(name, ImmutableList.of(), type);
  }

  private void parseDeclareFun(List<SExpr> items) {
    if (items.size() != 4 || !items.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed declare-fun command");
    }
    String name = decodeIdentifier(items.get(1).getAtom());
    List<SExpr> argSortExprs = items.get(2).getList();
    List<LeanSmtType> argTypes = new ArrayList<>(argSortExprs.size());
    boolean unsupported = false;
    for (SExpr argSort : argSortExprs) {
      @Nullable LeanSmtType t = parseSortOrNull(argSort);
      if (t == null) {
        unsupported = true;
      } else {
        argTypes.add(t);
      }
    }
    @Nullable LeanSmtType returnType = parseSortOrNull(items.get(3));
    if (returnType == null || unsupported) {
      unsupportedSymbols.add(name);
      return;
    }
    declareSymbol(name, argTypes, returnType);
  }

  private void parseDefineConst(List<SExpr> items) {
    if (items.size() != 4 || !items.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed define-const command");
    }
    String name = decodeIdentifier(items.get(1).getAtom());
    if (symbols.containsKey(name)
        || constantDefinitions.containsKey(name)
        || macroDefinitions.containsKey(name)) {
      throw new IllegalArgumentException("Redefinition is not supported for symbol: " + name);
    }
    @Nullable LeanSmtType type = parseSortOrNull(items.get(2));
    if (type == null) {
      unsupportedSymbols.add(name);
      return;
    }
    Term value = parseExpr(items.get(3), type, Map.of());
    constantDefinitions.put(name, value);
  }

  private void parseDefineFun(List<SExpr> items) {
    if (items.size() != 5 || !items.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed define-fun command");
    }
    String name = decodeIdentifier(items.get(1).getAtom());
    if (symbols.containsKey(name)
        || constantDefinitions.containsKey(name)
        || macroDefinitions.containsKey(name)) {
      throw new IllegalArgumentException("Redefinition is not supported for symbol: " + name);
    }

    List<SExpr> paramDecls = items.get(2).getList();
    @Nullable LeanSmtType returnType = parseSortOrNull(items.get(3));
    if (returnType == null) {
      unsupportedSymbols.add(name);
      return;
    }
    if (paramDecls.isEmpty()) {
      Term value = parseExpr(items.get(4), returnType, Map.of());
      constantDefinitions.put(name, value);
      return;
    }

    ImmutableList.Builder<ParamDecl> params = ImmutableList.builder();
    for (SExpr paramDecl : paramDecls) {
      List<SExpr> p = paramDecl.getList();
      if (p.size() != 2 || !p.get(0).isAtom()) {
        throw new IllegalArgumentException("Malformed define-fun parameter declaration");
      }
      @Nullable LeanSmtType paramType = parseSortOrNull(p.get(1));
      if (paramType == null) {
        unsupportedSymbols.add(name);
        return;
      }
      params.add(new ParamDecl(decodeIdentifier(p.get(0).getAtom()), paramType));
    }
    macroDefinitions.put(name, new MacroDef(params.build(), returnType, items.get(4)));
  }

  private void parseAssert(List<SExpr> items, List<Term> assertions) {
    if (items.size() != 2) {
      throw new IllegalArgumentException("Malformed assert command");
    }
    assertions.add(parseExpr(items.get(1), LeanSmtType.BOOL, Map.of()));
  }

  private void declareSymbol(String name, List<LeanSmtType> argTypes, LeanSmtType returnType) {
    SymbolDecl existing = symbols.get(name);
    if (argTypes.isEmpty()) {
      if (existing == null) {
        creator.makeVariable(returnType, name);
        symbols.put(name, SymbolDecl.variable(returnType));
        return;
      }
      if (existing.kind != SymbolKind.VARIABLE || !existing.variableType.equals(returnType)) {
        throw new IllegalArgumentException("Conflicting declaration for symbol: " + name);
      }
      return;
    }

    LeanSmtFunctionDecl decl =
        new LeanSmtFunctionDecl(
            name, FunctionDeclarationKind.UF, returnType, ImmutableList.copyOf(argTypes));
    if (existing == null) {
      symbols.put(name, SymbolDecl.function(decl));
      return;
    }
    if (existing.kind != SymbolKind.FUNCTION || !isSameSignature(existing.functionDecl, decl)) {
      throw new IllegalArgumentException("Conflicting declaration for function: " + name);
    }
  }

  private static boolean isSameSignature(LeanSmtFunctionDecl left, LeanSmtFunctionDecl right) {
    return left.getReturnType().equals(right.getReturnType())
        && left.getArgumentTypes().equals(right.getArgumentTypes());
  }

  private Term parseExpr(SExpr expr, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    Term term = expr.isAtom() ? parseAtom(expr.getAtom(), expectedType, locals) : parseListExpr(expr.getList(), expectedType, locals);
    if (expectedType != null && !term.type.equals(expectedType)) {
      throw new IllegalArgumentException(
          "Type mismatch, expected " + expectedType + " but got " + term.type);
    }
    return term;
  }

  private Term parseAtom(String token, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    String decodedToken = decodeIdentifier(token);
    if ("true".equals(token)) {
      return new Term(creator.getTrueHandle(), LeanSmtType.BOOL);
    }
    if ("false".equals(token)) {
      return new Term(creator.getFalseHandle(), LeanSmtType.BOOL);
    }
    if (token.startsWith("#b") || token.startsWith("#x")) {
      return parseBitvectorLiteral(token, expectedType);
    }

    Term local = locals.get(decodedToken);
    if (local != null) {
      return local;
    }
    Term def = constantDefinitions.get(decodedToken);
    if (def != null) {
      return def;
    }
    if (isNumeralAtom(token)) {
      return parseNumeral(token, expectedType);
    }

    SymbolDecl symbol = symbols.get(decodedToken);
    if (symbol == null) {
      if (unsupportedSymbols.contains(decodedToken)) {
        throw new IllegalArgumentException("Symbol uses unsupported sort in LeanSMT parser: " + token);
      }
      throw new IllegalArgumentException("Undeclared symbol in SMT-LIB input: " + token);
    }
    if (symbol.kind != SymbolKind.VARIABLE) {
      throw new IllegalArgumentException("Function symbol used without arguments: " + token);
    }
    return new Term(creator.makeVariable(symbol.variableType, decodedToken), symbol.variableType);
  }

  private Term parseListExpr(List<SExpr> expr, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    if (expr.isEmpty()) {
      throw new IllegalArgumentException("Malformed expression in SMT-LIB input");
    }
    if (!expr.get(0).isAtom()) {
      return parseIndexedApplication(expr, expectedType, locals);
    }
    String opToken = expr.get(0).getAtom();
    String op = decodeIdentifier(opToken);
    List<SExpr> args = expr.subList(1, expr.size());

    SymbolDecl maybeUf = symbols.get(op);
    if (maybeUf != null && maybeUf.kind == SymbolKind.FUNCTION) {
      return parseUfCall(op, maybeUf.functionDecl, args, locals);
    }

    MacroDef macro = macroDefinitions.get(op);
    if (macro != null) {
      return parseMacroCall(op, macro, args, expectedType, locals);
    }

    @Nullable Term parsed = parseCoreOperator(opToken, op, args, expectedType, locals);
    if (parsed != null) {
      return parsed;
    }

    parsed = parseBitvectorOperator(opToken, op, args, locals);
    if (parsed != null) {
      return parsed;
    }

    if (unsupportedSymbols.contains(op)) {
      throw new IllegalArgumentException("Symbol uses unsupported sort in LeanSMT parser: " + opToken);
    }
    throw new IllegalArgumentException("Unsupported SMT-LIB operator for LeanSMT parser: " + opToken);
  }

  private @Nullable Term parseCoreOperator(
      String opToken,
      String op,
      List<SExpr> args,
      @Nullable LeanSmtType expectedType,
      Map<String, Term> locals) {
    switch (opToken) {
      case "_":
        return parseIndexedLiteral(args, expectedType);
      case "let":
        return parseLet(args, expectedType, locals);
      case "not":
        checkArity(op, args, 1);
        return unaryBool(op, FunctionDeclarationKind.NOT, args.get(0), locals);
      case "and":
        return naryBool(op, FunctionDeclarationKind.AND, args, locals);
      case "or":
        return naryBool(op, FunctionDeclarationKind.OR, args, locals);
      case "xor":
        return naryBool(op, FunctionDeclarationKind.XOR, args, locals);
      case "=>":
        return naryBool(op, FunctionDeclarationKind.IMPLIES, args, locals);
      case "=":
        return chainEq(args, locals);
      case "distinct":
        return distinct(args, locals);
      case "<":
        return chainCompare(op, FunctionDeclarationKind.LT, args, locals);
      case "<=":
        return chainCompare(op, FunctionDeclarationKind.LTE, args, locals);
      case ">":
        return chainCompare(op, FunctionDeclarationKind.GT, args, locals);
      case ">=":
        return chainCompare(op, FunctionDeclarationKind.GTE, args, locals);
      case "+":
        return naryArith(op, FunctionDeclarationKind.ADD, args, expectedType, locals);
      case "-":
        return minus(args, expectedType, locals);
      case "*":
        return naryArith(op, FunctionDeclarationKind.MUL, args, expectedType, locals);
      case "div":
      case "/":
        checkArity(op, args, 2);
        return binaryArith(
            op, FunctionDeclarationKind.DIV, args.get(0), args.get(1), expectedType, locals);
      case "mod":
        checkArity(op, args, 2);
        Term lhs = parseExpr(args.get(0), LeanSmtType.INT, locals);
        Term rhs = parseExpr(args.get(1), LeanSmtType.INT, locals);
        return new Term(
            creator.makeBinary(
                "mod",
                FunctionDeclarationKind.MODULO,
                FormulaType.IntegerType,
                lhs.handle,
                rhs.handle,
                LeanSmtNativeApi::mkMod),
            LeanSmtType.INT);
      case "ite":
        checkArity(op, args, 3);
        Term cond = parseExpr(args.get(0), LeanSmtType.BOOL, locals);
        Term thenBranch = parseExpr(args.get(1), expectedType, locals);
        Term elseBranch = parseExpr(args.get(2), thenBranch.type, locals);
        return new Term(
            creator.makeTernary(
                "ite",
                FunctionDeclarationKind.ITE,
                thenBranch.type.toFormulaType(),
                cond.handle,
                thenBranch.handle,
                elseBranch.handle,
                LeanSmtNativeApi::mkIte),
            thenBranch.type);
      default:
        return null;
    }
  }

  private @Nullable Term parseBitvectorOperator(
      String opToken, String op, List<SExpr> args, Map<String, Term> locals) {
    switch (opToken) {
      case "concat":
        checkArity(op, args, 2);
        return bitvectorConcat(op, args.get(0), args.get(1), locals);
      case "bvnot":
        checkArity(op, args, 1);
        return bitvectorUnary(op, FunctionDeclarationKind.BV_NOT, args.get(0), locals);
      case "bvneg":
        checkArity(op, args, 1);
        return bitvectorUnary(op, FunctionDeclarationKind.BV_NEG, args.get(0), locals);
      case "bvand":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_AND, args.get(0), args.get(1), locals);
      case "bvor":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_OR, args.get(0), args.get(1), locals);
      case "bvxor":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_XOR, args.get(0), args.get(1), locals);
      case "bvadd":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_ADD, args.get(0), args.get(1), locals);
      case "bvsub":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_SUB, args.get(0), args.get(1), locals);
      case "bvmul":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_MUL, args.get(0), args.get(1), locals);
      case "bvudiv":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_UDIV, args.get(0), args.get(1), locals);
      case "bvsdiv":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_SDIV, args.get(0), args.get(1), locals);
      case "bvurem":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_UREM, args.get(0), args.get(1), locals);
      case "bvsrem":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_SREM, args.get(0), args.get(1), locals);
      case "bvsmod":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_SMOD, args.get(0), args.get(1), locals);
      case "bvshl":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_SHL, args.get(0), args.get(1), locals);
      case "bvlshr":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_LSHR, args.get(0), args.get(1), locals);
      case "bvashr":
        checkArity(op, args, 2);
        return bitvectorBinary(op, FunctionDeclarationKind.BV_ASHR, args.get(0), args.get(1), locals);
      case "bvult":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_ULT, args.get(0), args.get(1), locals);
      case "bvule":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_ULE, args.get(0), args.get(1), locals);
      case "bvugt":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_UGT, args.get(0), args.get(1), locals);
      case "bvuge":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_UGE, args.get(0), args.get(1), locals);
      case "bvslt":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_SLT, args.get(0), args.get(1), locals);
      case "bvsle":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_SLE, args.get(0), args.get(1), locals);
      case "bvsgt":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_SGT, args.get(0), args.get(1), locals);
      case "bvsge":
        checkArity(op, args, 2);
        return bitvectorCompare(op, FunctionDeclarationKind.BV_SGE, args.get(0), args.get(1), locals);
      case "rotate_left":
        checkArity(op, args, 2);
        return bitvectorRotateSymbolic(
            op, FunctionDeclarationKind.BV_ROTATE_LEFT, args.get(0), args.get(1), locals);
      case "rotate_right":
        checkArity(op, args, 2);
        return bitvectorRotateSymbolic(
            op, FunctionDeclarationKind.BV_ROTATE_RIGHT, args.get(0), args.get(1), locals);
      case "ubv_to_int":
        checkArity(op, args, 1);
        return bitvectorToInteger(op, FunctionDeclarationKind.UBV_TO_INT, args.get(0), locals);
      case "sbv_to_int":
        checkArity(op, args, 1);
        return bitvectorToInteger(op, FunctionDeclarationKind.SBV_TO_INT, args.get(0), locals);
      default:
        return null;
    }
  }

  private Term parseLet(List<SExpr> args, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    checkArity("let", args, 2);
    List<SExpr> bindings = args.get(0).getList();

    // SMT-LIB let-bindings are simultaneous: evaluate all RHS in outer scope.
    Map<String, Term> rhsValues = new LinkedHashMap<>();
    for (SExpr binding : bindings) {
      List<SExpr> pair = binding.getList();
      if (pair.size() != 2 || !pair.get(0).isAtom()) {
        throw new IllegalArgumentException("Malformed let binding");
      }
      String name = decodeIdentifier(pair.get(0).getAtom());
      rhsValues.put(name, parseExpr(pair.get(1), null, locals));
    }

    Map<String, Term> nested = new LinkedHashMap<>(locals);
    nested.putAll(rhsValues);
    return parseExpr(args.get(1), expectedType, nested);
  }

  private Term parseMacroCall(
      String name,
      MacroDef macro,
      List<SExpr> args,
      @Nullable LeanSmtType expectedType,
      Map<String, Term> locals) {
    if (macro.params.size() != args.size()) {
      throw new IllegalArgumentException(
          "define-fun arity mismatch for '"
              + name
              + "': expected "
              + macro.params.size()
              + " but got "
              + args.size());
    }
    Map<String, Term> nestedLocals = new LinkedHashMap<>(locals);
    for (int i = 0; i < args.size(); i++) {
      ParamDecl p = macro.params.get(i);
      nestedLocals.put(p.name, parseExpr(args.get(i), p.type, locals));
    }
    return parseExpr(macro.body, expectedType != null ? expectedType : macro.returnType, nestedLocals);
  }

  private Term parseUfCall(String name, LeanSmtFunctionDecl decl, List<SExpr> args, Map<String, Term> locals) {
    if (decl.getArgumentTypes().size() != args.size()) {
      throw new IllegalArgumentException(
          "UF arity mismatch for '"
              + name
              + "': expected "
              + decl.getArgumentTypes().size()
              + " but got "
              + args.size());
    }
    List<Long> handles = new ArrayList<>(args.size());
    for (int i = 0; i < args.size(); i++) {
      Term arg = parseExpr(args.get(i), decl.getArgumentTypes().get(i), locals);
      handles.add(arg.handle);
    }
    return new Term(creator.callFunctionImpl(decl, handles), decl.getReturnType());
  }

  private static String indexedSymbol(String op, int index) {
    return "(_ " + op + " " + index + ")";
  }

  private static String extractSymbol(int msb, int lsb) {
    return "(_ extract " + msb + " " + lsb + ")";
  }

  private Term parseIndexedApplication(
      List<SExpr> expr, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    List<SExpr> head = expr.get(0).getList();
    if (head.isEmpty() || !head.get(0).isAtom() || !"_".equals(head.get(0).getAtom())) {
      throw new IllegalArgumentException("Malformed indexed SMT-LIB operator");
    }
    if (head.size() < 3 || !head.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed indexed SMT-LIB operator");
    }
    String indexedOp = head.get(1).getAtom();
    List<SExpr> args = expr.subList(1, expr.size());

    switch (indexedOp) {
      case "extract":
        if (head.size() != 4 || !head.get(2).isAtom() || !head.get(3).isAtom()) {
          throw new IllegalArgumentException("Malformed extract index specification");
        }
        checkArity("(_ extract ...)", args, 1);
        int msb = parseNonNegativeIndex(head.get(2).getAtom());
        int lsb = parseNonNegativeIndex(head.get(3).getAtom());
        if (msb < lsb) {
          throw new IllegalArgumentException("Bitvector extract expects msb >= lsb");
        }
        Term extractArg = parseExpr(args.get(0), null, locals);
        if (!extractArg.type.isBitvector()) {
          throw new IllegalArgumentException("Bitvector extract expects bitvector argument");
        }
        int outWidth = msb - lsb + 1;
        return new Term(
            creator.makeUnary(
                extractSymbol(msb, lsb),
                FunctionDeclarationKind.BV_EXTRACT,
                FormulaType.getBitvectorTypeWithSize(outWidth),
                extractArg.handle,
                arg -> LeanSmtNativeApi.mkExtract(arg, msb, lsb)),
            LeanSmtType.bitvector(outWidth));

      case "zero_extend":
      case "sign_extend":
      case "rotate_left":
      case "rotate_right":
      case "int_to_bv":
      case "int2bv":
        if (head.size() != 3 || !head.get(2).isAtom()) {
          throw new IllegalArgumentException("Malformed indexed operator: " + indexedOp);
        }
        checkArity("(_ " + indexedOp + " ...)", args, 1);
        int index = parseNonNegativeIndex(head.get(2).getAtom());
        return parseIndexedUnary(indexedOp, index, args.get(0), expectedType, locals);

      default:
        throw new IllegalArgumentException(
            "Unsupported indexed SMT-LIB operator for LeanSMT parser: " + indexedOp);
    }
  }

  private Term parseIndexedUnary(
      String indexedOp,
      int index,
      SExpr argExpr,
      @Nullable LeanSmtType expectedType,
      Map<String, Term> locals) {
    switch (indexedOp) {
      case "int_to_bv":
      case "int2bv":
        Term intArg = parseExpr(argExpr, LeanSmtType.INT, locals);
        return new Term(creator.makeIntToBitvectorTerm(index, intArg.handle), LeanSmtType.bitvector(index));

      case "zero_extend":
      case "sign_extend":
        Term extendArg = parseExpr(argExpr, null, locals);
        if (!extendArg.type.isBitvector()) {
          throw new IllegalArgumentException(indexedOp + " expects bitvector argument");
        }
        int resultWidth = extendArg.type.getBitvectorSize() + index;
        String symbol = indexedSymbol(indexedOp, index);
        FunctionDeclarationKind kind =
            "sign_extend".equals(indexedOp)
                ? FunctionDeclarationKind.BV_SIGN_EXTENSION
                : FunctionDeclarationKind.BV_ZERO_EXTENSION;
        return new Term(
            creator.makeUnary(
                symbol,
                kind,
                FormulaType.getBitvectorTypeWithSize(resultWidth),
                extendArg.handle,
                arg -> LeanSmtNativeApi.mkIndexedApp1(indexedOp, index, arg)),
            LeanSmtType.bitvector(resultWidth));

      case "rotate_left":
      case "rotate_right":
        Term rotateArg = parseExpr(argExpr, expectedType, locals);
        if (!rotateArg.type.isBitvector()) {
          throw new IllegalArgumentException(indexedOp + " expects bitvector argument");
        }
        FunctionDeclarationKind rotateKind =
            "rotate_left".equals(indexedOp)
                ? FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT
                : FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT;
        return new Term(
            creator.makeUnary(
                indexedSymbol(indexedOp, index),
                rotateKind,
                rotateArg.type.toFormulaType(),
                rotateArg.handle,
                arg -> LeanSmtNativeApi.mkIndexedApp1(indexedOp, index, arg)),
            rotateArg.type);

      default:
        throw new IllegalArgumentException(
            "Unsupported indexed SMT-LIB unary operator for LeanSMT parser: " + indexedOp);
    }
  }

  private Term parseIndexedLiteral(List<SExpr> args, @Nullable LeanSmtType expectedType) {
    if (args.size() != 2 || !args.get(0).isAtom() || !args.get(1).isAtom()) {
      throw new IllegalArgumentException("Malformed indexed literal in SMT-LIB input");
    }
    String head = args.get(0).getAtom();
    if (!head.startsWith("bv")) {
      throw new IllegalArgumentException("Unsupported indexed literal in SMT-LIB input: " + head);
    }
    BigInteger value;
    try {
      value = new BigInteger(head.substring(2));
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException("Invalid bitvector literal value: " + head, e);
    }
    int width = parseNonNegativeIndex(args.get(1).getAtom());
    if (width == 0) {
      throw new IllegalArgumentException("Bitvector width must be positive");
    }
    if (expectedType != null && (!expectedType.isBitvector() || expectedType.getBitvectorSize() != width)) {
      throw new IllegalArgumentException(
          "Type mismatch, expected " + expectedType + " but got (_ BitVec " + width + ")");
    }
    BigInteger normalized = normalizeBitvectorValue(value, width);
    return new Term(creator.makeBitvectorConstant(width, normalized), LeanSmtType.bitvector(width));
  }

  private Term parseBitvectorLiteral(String token, @Nullable LeanSmtType expectedType) {
    int width;
    BigInteger value;
    if (token.startsWith("#b")) {
      String bits = token.substring(2);
      if (bits.isEmpty()) {
        throw new IllegalArgumentException("Invalid bitvector literal: " + token);
      }
      width = bits.length();
      value = new BigInteger(bits, 2);
    } else {
      String hex = token.substring(2);
      if (hex.isEmpty()) {
        throw new IllegalArgumentException("Invalid bitvector literal: " + token);
      }
      width = hex.length() * 4;
      value = new BigInteger(hex, 16);
    }

    if (expectedType != null) {
      if (!expectedType.isBitvector()) {
        throw new IllegalArgumentException("Bitvector literal used with non-bitvector type " + expectedType);
      }
      width = expectedType.getBitvectorSize();
    }

    BigInteger normalized = normalizeBitvectorValue(value, width);
    return new Term(creator.makeBitvectorConstant(width, normalized), LeanSmtType.bitvector(width));
  }

  private static BigInteger normalizeBitvectorValue(BigInteger value, int width) {
    BigInteger modulus = BigInteger.ONE.shiftLeft(width);
    BigInteger normalized = value.mod(modulus);
    if (normalized.signum() < 0) {
      normalized = normalized.add(modulus);
    }
    return normalized;
  }

  private static int parseNonNegativeIndex(String raw) {
    try {
      int value = Integer.parseInt(raw);
      if (value < 0) {
        throw new IllegalArgumentException("Negative numerals are forbidden in indices");
      }
      return value;
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException("Invalid indexed numeral: " + raw, e);
    }
  }

  private Term bitvectorUnary(
      String op, FunctionDeclarationKind kind, SExpr argExpr, Map<String, Term> locals) {
    Term arg = parseExpr(argExpr, null, locals);
    if (!arg.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector argument");
    }
    return new Term(
        creator.makeUnary(op, kind, arg.type.toFormulaType(), arg.handle, t -> LeanSmtNativeApi.mkApp1(op, t)),
        arg.type);
  }

  private Term bitvectorToInteger(
      String op, FunctionDeclarationKind kind, SExpr argExpr, Map<String, Term> locals) {
    Term arg = parseExpr(argExpr, null, locals);
    if (!arg.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector argument");
    }
    return new Term(
        creator.makeUnary(op, kind, FormulaType.IntegerType, arg.handle, t -> LeanSmtNativeApi.mkApp1(op, t)),
        LeanSmtType.INT);
  }

  private Term bitvectorBinary(
      String op, FunctionDeclarationKind kind, SExpr lhsExpr, SExpr rhsExpr, Map<String, Term> locals) {
    Term lhs = parseExpr(lhsExpr, null, locals);
    if (!lhs.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector arguments");
    }
    Term rhs = parseExpr(rhsExpr, lhs.type, locals);
    return new Term(
        creator.makeBinary(
            op, kind, lhs.type.toFormulaType(), lhs.handle, rhs.handle, (a, b) -> LeanSmtNativeApi.mkApp2(op, a, b)),
        lhs.type);
  }

  private Term bitvectorConcat(
      String op, SExpr lhsExpr, SExpr rhsExpr, Map<String, Term> locals) {
    Term lhs = parseExpr(lhsExpr, null, locals);
    Term rhs = parseExpr(rhsExpr, null, locals);
    if (!lhs.type.isBitvector() || !rhs.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector arguments");
    }
    int outWidth = lhs.type.getBitvectorSize() + rhs.type.getBitvectorSize();
    LeanSmtType outType = LeanSmtType.bitvector(outWidth);
    return new Term(
        creator.makeBinary(
            op,
            FunctionDeclarationKind.BV_CONCAT,
            outType.toFormulaType(),
            lhs.handle,
            rhs.handle,
            (a, b) -> LeanSmtNativeApi.mkApp2(op, a, b)),
        outType);
  }

  private Term bitvectorCompare(
      String op, FunctionDeclarationKind kind, SExpr lhsExpr, SExpr rhsExpr, Map<String, Term> locals) {
    Term lhs = parseExpr(lhsExpr, null, locals);
    if (!lhs.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector arguments");
    }
    Term rhs = parseExpr(rhsExpr, lhs.type, locals);
    return new Term(
        creator.makeBinary(
            op,
            kind,
            FormulaType.BooleanType,
            lhs.handle,
            rhs.handle,
            (a, b) -> LeanSmtNativeApi.mkApp2(op, a, b)),
        LeanSmtType.BOOL);
  }

  private Term bitvectorRotateSymbolic(
      String op, FunctionDeclarationKind kind, SExpr lhsExpr, SExpr rhsExpr, Map<String, Term> locals) {
    Term lhs = parseExpr(lhsExpr, null, locals);
    if (!lhs.type.isBitvector()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects bitvector arguments");
    }
    Term rhs = parseExpr(rhsExpr, lhs.type, locals);
    LeanSmtFormulaCreator.NativeBinary nativeOp =
        kind == FunctionDeclarationKind.BV_ROTATE_LEFT
            ? creator::buildRotateLeftTerm
            : creator::buildRotateRightTerm;
    return new Term(
        creator.makeBinary(op, kind, lhs.type.toFormulaType(), lhs.handle, rhs.handle, nativeOp),
        lhs.type);
  }

  private Term unaryBool(String op, FunctionDeclarationKind kind, SExpr argExpr, Map<String, Term> locals) {
    Term arg = parseExpr(argExpr, LeanSmtType.BOOL, locals);
    return new Term(
        creator.makeUnary(op, kind, FormulaType.BooleanType, arg.handle, LeanSmtNativeApi::mkNot),
        LeanSmtType.BOOL);
  }

  private Term naryBool(String op, FunctionDeclarationKind kind, List<SExpr> args, Map<String, Term> locals) {
    if (args.size() < 2) {
      throw new IllegalArgumentException("Operator '" + op + "' expects at least 2 arguments");
    }
    Term current = parseExpr(args.get(0), LeanSmtType.BOOL, locals);
    for (int i = 1; i < args.size(); i++) {
      Term next = parseExpr(args.get(i), LeanSmtType.BOOL, locals);
      LeanSmtFormulaCreator.NativeBinary nativeOp;
      switch (kind) {
        case AND:
          nativeOp = LeanSmtNativeApi::mkAnd;
          break;
        case OR:
          nativeOp = LeanSmtNativeApi::mkOr;
          break;
        case XOR:
          nativeOp = LeanSmtNativeApi::mkXor;
          break;
        case IMPLIES:
          nativeOp = LeanSmtNativeApi::mkImplies;
          break;
        default:
          throw new AssertionError("Unexpected boolean n-ary op kind " + kind);
      }
      current =
          new Term(
              creator.makeBinary(op, kind, FormulaType.BooleanType, current.handle, next.handle, nativeOp),
              LeanSmtType.BOOL);
    }
    return current;
  }

  private Term chainEq(List<SExpr> args, Map<String, Term> locals) {
    if (args.size() < 2) {
      throw new IllegalArgumentException("Operator '=' expects at least 2 arguments");
    }
    List<Term> parsed = new ArrayList<>(args.size());
    Term first = parseExpr(args.get(0), null, locals);
    parsed.add(first);
    for (int i = 1; i < args.size(); i++) {
      parsed.add(parseExpr(args.get(i), first.type, locals));
    }
    return foldPairwiseBoolean("=", FunctionDeclarationKind.EQ, parsed, LeanSmtNativeApi::mkEq);
  }

  private Term distinct(List<SExpr> args, Map<String, Term> locals) {
    if (args.size() < 2) {
      throw new IllegalArgumentException("Operator 'distinct' expects at least 2 arguments");
    }
    List<Term> parsed = new ArrayList<>(args.size());
    Term first = parseExpr(args.get(0), null, locals);
    parsed.add(first);
    for (int i = 1; i < args.size(); i++) {
      parsed.add(parseExpr(args.get(i), first.type, locals));
    }

    Term result = null;
    for (int i = 0; i < parsed.size(); i++) {
      for (int j = i + 1; j < parsed.size(); j++) {
        Term neq =
            new Term(
                creator.makeBinary(
                    "distinct",
                    FunctionDeclarationKind.DISTINCT,
                    FormulaType.BooleanType,
                    parsed.get(i).handle,
                    parsed.get(j).handle,
                    LeanSmtNativeApi::mkDistinct),
                LeanSmtType.BOOL);
        result = andMaybe(result, neq);
      }
    }
    return Preconditions.checkNotNull(result);
  }

  private Term chainCompare(String op, FunctionDeclarationKind kind, List<SExpr> args, Map<String, Term> locals) {
    if (args.size() < 2) {
      throw new IllegalArgumentException("Operator '" + op + "' expects at least 2 arguments");
    }
    List<Term> parsed = new ArrayList<>(args.size());
    Term first = parseExpr(args.get(0), null, locals);
    if (!first.type.isInt() && !first.type.isReal()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects numeric arguments");
    }
    parsed.add(first);
    for (int i = 1; i < args.size(); i++) {
      parsed.add(parseExpr(args.get(i), first.type, locals));
    }
    LeanSmtFormulaCreator.NativeBinary nativeOp;
    switch (kind) {
      case LT:
        nativeOp = LeanSmtNativeApi::mkLt;
        break;
      case LTE:
        nativeOp = LeanSmtNativeApi::mkLe;
        break;
      case GT:
        nativeOp = LeanSmtNativeApi::mkGt;
        break;
      case GTE:
        nativeOp = LeanSmtNativeApi::mkGe;
        break;
      default:
        throw new AssertionError("Unexpected comparison kind " + kind);
    }
    return foldPairwiseBoolean(op, kind, parsed, nativeOp);
  }

  private Term foldPairwiseBoolean(
      String symbol,
      FunctionDeclarationKind kind,
      List<Term> parsed,
      LeanSmtFormulaCreator.NativeBinary nativeOp) {
    Term result = null;
    for (int i = 1; i < parsed.size(); i++) {
      Term part =
          new Term(
              creator.makeBinary(
                  symbol,
                  kind,
                  FormulaType.BooleanType,
                  parsed.get(i - 1).handle,
                  parsed.get(i).handle,
                  nativeOp),
              LeanSmtType.BOOL);
      result = andMaybe(result, part);
    }
    return Preconditions.checkNotNull(result);
  }

  private Term andMaybe(@Nullable Term current, Term next) {
    if (current == null) {
      return next;
    }
    return new Term(
        creator.makeBinary(
            "and",
            FunctionDeclarationKind.AND,
            FormulaType.BooleanType,
            current.handle,
            next.handle,
            LeanSmtNativeApi::mkAnd),
        LeanSmtType.BOOL);
  }

  private Term naryArith(
      String op,
      FunctionDeclarationKind kind,
      List<SExpr> args,
      @Nullable LeanSmtType expectedType,
      Map<String, Term> locals) {
    if (args.size() < 2) {
      throw new IllegalArgumentException("Operator '" + op + "' expects at least 2 arguments");
    }
    Term current = parseExpr(args.get(0), expectedType, locals);
    if (!current.type.isInt() && !current.type.isReal()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects numeric arguments");
    }
    for (int i = 1; i < args.size(); i++) {
      Term next = parseExpr(args.get(i), current.type, locals);
      LeanSmtFormulaCreator.NativeBinary nativeOp =
          kind == FunctionDeclarationKind.ADD ? LeanSmtNativeApi::mkAdd : LeanSmtNativeApi::mkMul;
      current =
          new Term(
              creator.makeBinary(
                  op, kind, current.type.toFormulaType(), current.handle, next.handle, nativeOp),
              current.type);
    }
    return current;
  }

  private Term minus(List<SExpr> args, @Nullable LeanSmtType expectedType, Map<String, Term> locals) {
    if (args.isEmpty()) {
      throw new IllegalArgumentException("Operator '-' expects at least 1 argument");
    }
    if (args.size() == 1) {
      Term arg = parseExpr(args.get(0), expectedType, locals);
      if (!arg.type.isInt() && !arg.type.isReal()) {
        throw new IllegalArgumentException("Unary '-' expects numeric argument");
      }
      return new Term(
          creator.makeUnary(
              "-",
              FunctionDeclarationKind.UMINUS,
              arg.type.toFormulaType(),
              arg.handle,
              LeanSmtNativeApi::mkNeg),
          arg.type);
    }
    Term current = parseExpr(args.get(0), expectedType, locals);
    if (!current.type.isInt() && !current.type.isReal()) {
      throw new IllegalArgumentException("Operator '-' expects numeric arguments");
    }
    for (int i = 1; i < args.size(); i++) {
      Term next = parseExpr(args.get(i), current.type, locals);
      current =
          new Term(
              creator.makeBinary(
                  "-",
                  FunctionDeclarationKind.SUB,
                  current.type.toFormulaType(),
                  current.handle,
                  next.handle,
                  LeanSmtNativeApi::mkSub),
              current.type);
    }
    return current;
  }

  private Term binaryArith(
      String op,
      FunctionDeclarationKind kind,
      SExpr lhsExpr,
      SExpr rhsExpr,
      @Nullable LeanSmtType expectedType,
      Map<String, Term> locals) {
    Term lhs = parseExpr(lhsExpr, expectedType, locals);
    if (!lhs.type.isInt() && !lhs.type.isReal()) {
      throw new IllegalArgumentException("Operator '" + op + "' expects numeric arguments");
    }
    Term rhs = parseExpr(rhsExpr, lhs.type, locals);
    LeanSmtFormulaCreator.NativeBinary nativeOp =
        "/".equals(op) ? (left, right) -> LeanSmtNativeApi.mkApp2("/", left, right) : LeanSmtNativeApi::mkDiv;
    return new Term(
        creator.makeBinary(
            op, kind, lhs.type.toFormulaType(), lhs.handle, rhs.handle, nativeOp),
        lhs.type);
  }

  private static boolean isNumeralAtom(String token) {
    if (token.isEmpty()) {
      return false;
    }
    char c = token.charAt(0);
    return Character.isDigit(c) || c == '-' || token.contains(".") || token.contains("/");
  }

  private Term parseNumeral(String token, @Nullable LeanSmtType expectedType) {
    LeanSmtType targetType = expectedType;
    if (targetType == null) {
      targetType = (token.contains(".") || token.contains("/")) ? LeanSmtType.REAL : LeanSmtType.INT;
    }

    if (targetType.isInt()) {
      try {
        return new Term(creator.makeIntConstant(new BigInteger(token)), LeanSmtType.INT);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("Invalid integer literal: " + token, e);
      }
    }
    if (targetType.isReal()) {
      try {
        Rational rational;
        if (token.contains(".")) {
          rational = Rational.ofBigDecimal(new BigDecimal(token));
        } else if (token.contains("/")) {
          String[] parts = token.split("/", -1);
          if (parts.length != 2) {
            throw new NumberFormatException("Invalid rational form");
          }
          rational = Rational.of(new BigInteger(parts[0]), new BigInteger(parts[1]));
        } else {
          rational = Rational.ofBigInteger(new BigInteger(token));
        }
        return new Term(creator.makeRealConstant(rational), LeanSmtType.REAL);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("Invalid rational literal: " + token, e);
      }
    }
    throw new IllegalArgumentException("Unsupported numeral target type: " + targetType);
  }

  private static void checkArity(String op, List<SExpr> args, int expected) {
    if (args.size() != expected) {
      throw new IllegalArgumentException(
          "Operator '" + op + "' expects " + expected + " argument(s), got " + args.size());
    }
  }

  private static @Nullable LeanSmtType parseSortOrNull(SExpr sortExpr) {
    if (!sortExpr.isAtom()) {
      List<SExpr> s = sortExpr.getList();
      if (!s.isEmpty() && s.get(0).isAtom()) {
        String head = s.get(0).getAtom();
        if ("_".equals(head)
            && s.size() == 3
            && s.get(1).isAtom()
            && "BitVec".equals(s.get(1).getAtom())
            && s.get(2).isAtom()) {
          try {
            int width = Integer.parseInt(s.get(2).getAtom());
            if (width > 0) {
              return LeanSmtType.bitvector(width);
            }
          } catch (NumberFormatException e) {
            return null;
          }
        }
        if ("Array".equals(head) || "_".equals(head)) {
          return null;
        }
      }
      return null;
    }
    switch (sortExpr.getAtom()) {
      case "Bool":
        return LeanSmtType.BOOL;
      case "Int":
        return LeanSmtType.INT;
      case "Real":
        return LeanSmtType.REAL;
      case "Float32":
      case "Float64":
      case "String":
      case "RegLan":
        return null;
      default:
        return null;
    }
  }

  private static SExpr parseSExpr(String command) {
    Deque<String> tokens = tokenize(command);
    SExpr root = parseOne(tokens);
    if (!tokens.isEmpty()) {
      throw new IllegalArgumentException("Unexpected trailing tokens while parsing SMT-LIB command");
    }
    return root;
  }

  private static SExpr parseOne(Deque<String> tokens) {
    String token = tokens.pollFirst();
    if (token == null) {
      throw new IllegalArgumentException("Unexpected end of SMT-LIB command");
    }
    if ("(".equals(token)) {
      List<SExpr> items = new ArrayList<>();
      while (!tokens.isEmpty() && !")".equals(tokens.peekFirst())) {
        items.add(parseOne(tokens));
      }
      if (tokens.isEmpty()) {
        throw new IllegalArgumentException("Unbalanced parentheses in SMT-LIB command");
      }
      tokens.pollFirst();
      return SExpr.list(items);
    }
    if (")".equals(token)) {
      throw new IllegalArgumentException("Unexpected ')' in SMT-LIB command");
    }
    return SExpr.atom(token);
  }

  private static Deque<String> tokenize(String input) {
    Deque<String> out = new ArrayDeque<>();
    StringBuilder current = new StringBuilder();
    boolean inString = false;
    boolean inQuoted = false;
    for (int i = 0; i < input.length(); i++) {
      char c = input.charAt(i);
      if (inString) {
        current.append(c);
        if (c == '"') {
          inString = false;
        }
        continue;
      }
      if (inQuoted) {
        current.append(c);
        if (c == '|') {
          if (i + 1 < input.length() && input.charAt(i + 1) == '|') {
            current.append('|');
            i++;
          } else {
            inQuoted = false;
          }
        }
        continue;
      }
      if (c == '"') {
        flushToken(current, out);
        current.append(c);
        inString = true;
        continue;
      }
      if (c == '|') {
        flushToken(current, out);
        current.append(c);
        inQuoted = true;
        continue;
      }
      if (c == '(' || c == ')') {
        flushToken(current, out);
        out.addLast(Character.toString(c));
      } else if (Character.isWhitespace(c)) {
        flushToken(current, out);
      } else {
        current.append(c);
      }
    }
    flushToken(current, out);
    return out;
  }

  private static void flushToken(StringBuilder current, Deque<String> out) {
    if (current.length() > 0) {
      out.addLast(current.toString());
      current.setLength(0);
    }
  }

  private static String decodeIdentifier(String token) {
    if (token.length() >= 2 && token.startsWith("|") && token.endsWith("|")) {
      return token.substring(1, token.length() - 1).replace("||", "|");
    }
    return token;
  }
}
