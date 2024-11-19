// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Cmd_assertContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Cmd_declareConstContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Cmd_declareFunContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Cmd_popContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Cmd_pushContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Decl_sortContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Function_defContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Id_symbContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Id_symb_idxContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.MultisortContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.MultitermContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Qual_id_sortContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Resp_get_modelContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Sort_fpContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Sort_idContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_exclamContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_existsContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_forallContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_letContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_qual_idContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Term_spec_constContext;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.smtlibv2Parser.Var_bindingContext;
import scala.Tuple2;

/**
 * Implements a method from smtlibv2BaseVisitor for each node in a parse tree that requires some
 * form of action in order to transform the parsed SMT-LIB2 into JavaSMT.
 */
@SuppressWarnings({"CheckReturnValue", "unchecked"})
public class Visitor extends smtlibv2BaseVisitor<Object> {

  /**
   * saves all created Formulas that are not part of a let statement as ParserFormula objects with
   * their variable name or value as key.
   */
  // TODO Are these declarations?
  private final Map<String, ParserFormula> variables = new HashMap<>();

  /**
   * saves all created Formulas that are part of a let statement as ParserFormula objects with their
   * variable name or value as key.
   */
  // TODO They are declarations!
  private final Map<String, ParserFormula> letVariables = new HashMap<>();

  /** saves each 'assert' statement interpreted as a BooleanFormula object as an entry. */
  // TODO Here we collect the formulas
  private final List<BooleanFormula> constraints = new ArrayList<>();
  private final FormulaManager fmgr;
  private final BooleanFormulaManager bmgr;
  private final @Nullable IntegerFormulaManager imgr;
  private final @Nullable RationalFormulaManager rmgr;
  private final @Nullable BitvectorFormulaManager bimgr;
  private final @Nullable ArrayFormulaManager amgr;
  private final UFManager umgr;
  private final @Nullable FloatingPointFormulaManager fpmgr;
  List<Model.ValueAssignment> assignments = new ArrayList<>();

  // TODO Should we support push,etc?
  public List<BooleanFormula> getConstraints() {
    return constraints;
  }

  // TODO This seems to be used to collect function definitions in the model:
  //  Do we actually need it?
  public List<ValueAssignment> getAssignments() {
    return assignments;
  }

  /** is set to 'true' if a node 'model' is encountered. */
  private boolean isModel = false;

  // TODO Does the visitor use its own solver instance, or should the formulas be added to an
  //  existing instance?
  public Visitor(
      FormulaManager fmgr,
      BooleanFormulaManager bmgr,
      @Nullable IntegerFormulaManager imgr,
      @Nullable RationalFormulaManager rmgr,
      @Nullable BitvectorFormulaManager bimgr,
      @Nullable ArrayFormulaManager amgr,
      UFManager umgr,
      @Nullable FloatingPointFormulaManager fpmgr) {
    this.fmgr = fmgr;
    this.bmgr = bmgr;
    this.imgr = imgr;
    this.rmgr = rmgr;
    this.bimgr = bimgr;
    this.amgr = amgr;
    this.umgr = umgr;
    this.fpmgr = fpmgr;
  }

  @Override
  // TODO Is this for sort declarations? If so, we may not need it.
  public List<String> visitId_symb(Id_symbContext ctx) {
    List<String> sort = new ArrayList<>();
    sort.add(ctx.getText());
    return sort;
  }

  @Override
  public List<String> visitId_symb_idx(Id_symb_idxContext ctx) {
    List<String> sort = new ArrayList<>();
    sort.add(ctx.symbol().getText());
    for (int i = 0; i < ctx.index().size(); i++) {
      sort.add(ctx.index(i).getText());
    }
    return sort;
  }

  @Override
  public FormulaType.ArrayFormulaType<?, ?> visitMultisort(MultisortContext ctx) {
    FormulaType.ArrayFormulaType<?, ?> result;
    if (ctx.identifier().getText().equals("Array")) {
      FormulaType<?> idx = (FormulaType<?>) visit(ctx.sort(0));
      FormulaType<?> elem = (FormulaType<?>) visit(ctx.sort(1));
      result = FormulaType.getArrayType(idx, elem);
    } else {
      throw new ParserException(ctx.identifier().getText() + " is not a known sort. ");
    }

    return result;
  }

  /**
   * Returns all the first parts without numbers of legal Strings how a floating Point can be
   * defined in SMTLIB2 where Integers are used as exponent and mantissa.
   * @return ArrayList with the fitting strings
   */
  private static ArrayList<String> getAllAllowedFPBeginningsWithInts() {
    ArrayList<String> beginnings = new ArrayList<>();

    // Numeral FloatingPoint: (_ FloatingPoint 5 11)
    beginnings.add("(_ FloatingPoint");

    // FloatingPointPlusOrMinusInfinity: ((_ +oo eb sb) ...)
    beginnings.add("(_ +oo");
    beginnings.add("(_ -oo");

    // FloatingPointPlusOrMinusZero: ((_ +zero eb sb) ...)
    beginnings.add("(_ +zero");
    beginnings.add("(_ -zero");

    // NotANumberFloatingPoint: ((_ NaN eb sb) ...)
    beginnings.add("(_ NaN");

    return beginnings;
  }
  /**
   * Returns all the first parts without numbers of legal Strings how a floating Point can be
   * defined in SMTLIB2 where non-Integers are used, f.e. Bitvectors and Hexadecimal Floating-Points
   * @return ArrayList with the fitting strings
   */
  private static ArrayList<String> getAllAllowedFPBeginningsWithoutInts() {
    ArrayList<String> beginnings = new ArrayList<>();

    // FloatingPointShortVariant: (Float128)
    beginnings.add("(Float");

    // BinaryFloatingPoint: (fp #b)
    beginnings.add("(fp #b");

    // HexadecimalFloatingPoint: #x1.8p+1
    beginnings.add("#x");

    return beginnings;
  }

  /**
   * This method parses a bitvector or hexadecimal SMTLIB2-String to an integer.
   * @param input String in  hexadecimal or bitvector format according to smtlibv2
   * @return the parsed integer
   */
  public static int parseBitOrHexToInt(String input) {
    if (input.startsWith("#b")) {
      String binaryPart = input.substring(2);
      try {
        return Integer.parseInt(binaryPart, 2);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("invalid bit format: " + input, e);
      }
    } else if (input.startsWith("#x")) {
      String hexPart = input.substring(2);
      try {
        return Integer.parseInt(hexPart, 16);
      } catch (NumberFormatException e) {
        throw new IllegalArgumentException("invalid hex format: " + input, e);
      }
    } else {
      throw new IllegalArgumentException("string could not be detected as bitv or hex: " + input);
    }
  }

  /**
   * Checks if the beginning of the String matches one from a list.
   * @param checkedString String which beginning should be checked
   * @param listWithBeginnings ArrayList with the Strings that could match the checkedString
   * @return true if at least one item of the list matches the beginning of the String
   */
  public static boolean beginningMatchesList(String checkedString,
                                          ArrayList<String> listWithBeginnings){
    for(String x : listWithBeginnings){
      if(checkedString.startsWith(x)){
        return true;
      }
    }
    return false;
  }

  /**
   * Checks if the String has the format of a Bitvector in SMTLIBv2 and creates the matching
   * FormulaType.
   * @param type SMTLIB2 String (not a whole file, just one Formula)
   * @return matching FormulaType
   */
  public FormulaType<?> parseToBitVecFormulaTypeIfMatching(String type){
    String bvSize = "";
    if (type.startsWith("(_BitVec")) {
      bvSize = Iterables.get(Splitter.on("_BitVec").split(type), 1);
      bvSize = Iterables.get(Splitter.on(')').split(bvSize), 0);
      return FormulaType.getBitvectorTypeWithSize(Integer.parseInt(bvSize));
    }
    throw new ParserException("Invalid Bitvector format: " + type);

  }
  /**
   * Checks if the String has the format of a FloatingPoint in SMTLIBv2 and creates the matching
   * FormulaType.
   * @param type SMTLIB2 String (not a whole file, just one Formula)
   * @return matching FormulaType
   */
  public FormulaType<?> parseToFloatingPointFormulaTypeIfMatching(String type){
    if (beginningMatchesList(type, getAllAllowedFPBeginningsWithInts())){
      try {
        String[] parts = type.split(" ");
        int exponent = Integer.parseInt(parts[2]);
        int mantissa = Integer.parseInt(parts[3].replace(")", ""));
        return FormulaType.getFloatingPointType(exponent, mantissa);
      } catch (Exception e) {
        throw new ParserException("Invalid FloatingPoint format: " + type, e);
      }
    }
    if (beginningMatchesList(type, getAllAllowedFPBeginningsWithoutInts())) {
      if(type.startsWith("(Float16")){
        int exponent = 5;
        int mantissa = 11;
        return FormulaType.getFloatingPointType(exponent, mantissa);
      }
      if(type.startsWith("(Float32")){
        return FormulaType.getSinglePrecisionFloatingPointType();
      }
      if(type.startsWith("(Float64")){
        return FormulaType.getDoublePrecisionFloatingPointType();
      }
      if(type.startsWith("(Float128")){
        int exponent = 15;
        int mantissa = 113;
        return FormulaType.getFloatingPointType(exponent, mantissa);
      }
      if(type.startsWith("(fp")){
        //NOT TO BE HANDLED HERE - see visitSpec_Const
      }
      if(type.startsWith("#x")){
        //NOT TO BE HANDLED HERE - see visitSpec_Const
      }
    }
    throw new ParserException("Invalid Floating Point Format: " + type);
  }

  /**
   * Sees if a SMT2 String is a Bitvector
   * @param smt2 Smt2 String
   * @return true if it starts with "(_Bitvec"
   */
  public static boolean isABitVecInSMT2(String smt2){
    return smt2.startsWith("(_BitVec");
  }

  /**
   * Sees if SMT2 String is a FloatingPoint by comparing it's beginning to the accepted ways of
   * defining a Floating-Point in SMT2
   * @param smt2 String in smt2 format
   * @return true if at least one beginning is matched
   */
  public static boolean isAFloatingPointInSMT2(String smt2){
    return beginningMatchesList(smt2, getAllAllowedFPBeginningsWithoutInts())
        || beginningMatchesList(smt2, getAllAllowedFPBeginningsWithoutInts());
  }


  @Override
  public FormulaType<?> visitSort_id(Sort_idContext ctx) {
    String type = ctx.getText();

    if(isABitVecInSMT2(type)){
      return parseToBitVecFormulaTypeIfMatching(type);
    }
    if(isAFloatingPointInSMT2(type)){
      return parseToFloatingPointFormulaTypeIfMatching(type);
    }

    switch (type) {
      case "Int":
        return FormulaType.IntegerType;
      case "Bool":
        return FormulaType.BooleanType;
      case "Real":
        return FormulaType.RationalType;
      default:
        throw new ParserException(type + " is not a known Array sort. ");
    }
  }

  @Override
  public Tuple2<String, FormulaType<?>> visitQual_id_sort(Qual_id_sortContext ctx) {
    String operator = ctx.identifier().getText();
    FormulaType<?> sort = (FormulaType<?>) visit(ctx.sort());
    Tuple2<String, FormulaType<?>> result = new Tuple2<>(operator, sort);
    return result;
  }

  @Override
  public Object visitVar_binding(Var_bindingContext ctx) {
    String name = ctx.symbol().getText();
    Formula formula = (Formula) visit(ctx.term());
    letVariables.put(name, new ParserFormula(formula));
    return visitChildren(ctx);
  }

  public static boolean isInteger(String strNum) {
    try {
      Integer.parseInt(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isFloat(String strNum) {
    try {
      Float.parseFloat(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isDouble(String strNum) {
    try {
      Double.parseDouble(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isLong(String strNum) {
    try {
      Long.parseLong(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isBigInteger(String strNum) {
    boolean ret = true;
    try {
      BigInteger x = new BigInteger(strNum);
      if (!x.equals(new BigInteger(strNum))) {
        ret = false;
      }
    } catch (NumberFormatException nfe) {
      return false;
    }
    return ret;
  }

  // TODO Use an enum here
  public static String getNumericType(String strNum) {
    if (isInteger(strNum)) {
      return "Integer";
    } else if (isLong(strNum)) {
      return "Long";
    } else if (isBigInteger(strNum)) {
      return "BigInteger";
    } else if (isFloat(strNum)) {
      return "Float";
    } else if (isDouble(strNum)) {
      return "Double";
    } else {
      return "other";
    }
  }

  @Override
  public Object visitTerm_spec_const(Term_spec_constContext ctx) {
    String operand = ctx.getText();
    if (variables.containsKey(operand)) {
      return variables.get(operand).javaSmt;
    } else if (getNumericType(operand).equals("Integer")
        || getNumericType(operand).equals("Long")
        || getNumericType(operand).equals("BigInteger")) {
      variables.put(operand, new ParserFormula(Objects.requireNonNull(imgr).makeNumber(operand)));
      return variables.get(operand).javaSmt;
    } else if (getNumericType(operand).equals("Double")
        || getNumericType(operand).equals("Float")) {
      variables.put(operand, new ParserFormula(Objects.requireNonNull(rmgr).makeNumber(operand)
          ));
      //TODO: I think this needs to be changed to using the fpmgr. MIT DANIEL ABSPRECHEN
      return variables.get(operand).javaSmt;
    }
    //TODO: add floating Point recognization if rationals are used, that aren't "floats" or doubles
    /*
    else if (false){
      variables.put(operand, new ParserFormula(Objects.requireNonNull(fpmgr).makeNumber(operand,
          FloatingPointType.getSinglePrecisionFloatingPointType())));
    }else if(getNumericType(operand).equals("Double")){
      variables.put(operand, new ParserFormula(Objects.requireNonNull(fpmgr).makeNumber(operand,
          FloatingPointType.getDoublePrecisionFloatingPointType())));
           }
     */


    else if (operand.startsWith("#b")) {
      String binVal = Iterables.get(Splitter.on('b').split(operand), 1);
      int index = binVal.length();
      int value = Integer.parseInt(binVal, 2);
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    } else if (operand.startsWith("#x")) {
      String hexVal = Iterables.get(Splitter.on('x').split(operand), 1);
      int index = (hexVal.length() * 4);
      BigInteger value = new BigInteger(hexVal, 16);
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    }
    else {
      throw new ParserException("Operand " + operand + " is unknown.");
    }
  }

  @Override
  public Object visitTerm_qual_id(Term_qual_idContext ctx) {
    String operand = replaceReservedChars(ctx.getText());
    List<String> bitVec = (List<String>) visitChildren(ctx);
    if (letVariables.containsKey(operand)) {
      if (!(letVariables.get(operand).type == null)
          && Objects.equals(letVariables.get(operand).type, "UF")
          && letVariables.get(operand).inputParams == null) {
        return umgr.callUF(
            (FunctionDeclaration<Formula>) letVariables.get(operand).javaSmt, new ArrayList<>());
      }
      return letVariables.get(operand).javaSmt;
    } else if (variables.containsKey(operand)) {
      if (!(variables.get(operand).type == null)
          && Objects.equals(variables.get(operand).type, "UF")
          && !(variables.get(operand).inputParams == null)
          && Objects.requireNonNull(variables.get(operand).inputParams).isEmpty()) {
        return umgr.callUF(
            (FunctionDeclaration<Formula>) variables.get(operand).javaSmt, new ArrayList<>());
      }
      return variables.get(operand).javaSmt;
    } else if (operand.equals("false")) {
      variables.put(operand, new ParserFormula(bmgr.makeFalse()));
      return variables.get(operand).javaSmt;
    } else if (operand.equals("true")) {
      variables.put(operand, new ParserFormula(bmgr.makeTrue()));
      return variables.get(operand).javaSmt;
    } else if (!bitVec.isEmpty()) {
      BigInteger value = new BigInteger(Iterables.get(Splitter.on('v').split(bitVec.get(0)), 1));
      int index = Integer.parseInt(bitVec.get(1));
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    } else {
      throw new ParserException("Operand " + operand + " is unknown.");
    }
  }

  /**
   * gets the operands used in a nested term.
   *
   * @param ctx current MultitermContext
   * @param operands List of the operands transformed to Formula objects
   */
  public void getOperands(MultitermContext ctx, List<Formula> operands) {

    for (int i = 0; i < ctx.term().size(); ++i) {
      Object operand = visit(ctx.term(i));
      if (operand != null) {
        operands.add((Formula) operand);
      }
    }
  }

  // TODO Can we get a better return type?
  @Override
  public Object visitMultiterm(MultitermContext ctx) {
    Object identifier = visit(ctx.qual_identifer());
    List<String> operators = null;
    String operator = "";
    FormulaType<?> sort = null;
    if (identifier instanceof List) {
      operators = (List<String>) identifier;
      operator = Objects.requireNonNull(operators).get(0);
    } else if (identifier instanceof Tuple2) {
      operator = ((Tuple2<String, FormulaType<?>>) identifier)._1;
      sort = ((Tuple2<String, FormulaType<?>>) identifier)._2;
    }
    operator = replaceReservedChars(operator);

    Object ufOperator = null;
    if (variables.containsKey(operator)) {
      ufOperator = variables.get(operator).javaSmt;
      operator = "UF";
    }

    List<Formula> operands = new ArrayList<>();
    getOperands(ctx, operands);
    switch (operator) {
      case "and":
        try {
          List<BooleanFormula> booleanOperands =
              operands.stream().map(e -> (BooleanFormula) e).collect(Collectors.toList());
          return bmgr.and(booleanOperands);
        } catch (Exception e) {
          throw new ParserException("Operands for " + operator + " need to be of Boolean type");
        }
      case "or":
        try {
          List<BooleanFormula> booleanOperands =
              operands.stream().map(e -> (BooleanFormula) e).collect(Collectors.toList());
          return bmgr.or(booleanOperands);
        } catch (Exception e) {
          throw new ParserException("Operands for " + operator + " need to be of Boolean type");
        }
      case "xor":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.xor((BooleanFormula) it.next(), (BooleanFormula) it.next());
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of Boolean type");
          }
        }
      case "not":
        if (operands.size() != 1) {
          throw new ParserException(operator + " takes one boolean operand as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.not((BooleanFormula) it.next());
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of Boolean type");
          }
        }
      case "=>":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.implication((BooleanFormula) it.next(), (BooleanFormula) it.next());
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of Boolean type");
          }
        }
      case "ite":
        if (operands.size() != 3) {
          throw new ParserException(operator + " takes three boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.ifThenElse((BooleanFormula) it.next(), it.next(), it.next());
          } catch (Exception e) {
            throw new ParserException(
                "Condition for "
                    + operator
                    + " need to be of Boolean type and the types of both branches need to match.");
          }
        }
      case "+":
        // numeral operators
        if (!operands.isEmpty()) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).sum(numeralOperands);
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).sum(integerOperands);
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes at least one numeral operand as input. ");
        }
      case "-":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .subtract(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .subtract(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else if (operands.size() == 1) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).negate(numeralOperands.get(0));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).negate(integerOperands.get(0));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(
              operator + " takes either one or two numeral operands as input. ");
        }
      case "div":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .divide(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .divide(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }
      case "mod":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              throw new ParserException(operator + " is not available for Reals. ");
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .modulo(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of integer type");
          }
        } else {
          throw new ParserException(operator + " takes two integer operands as input. ");
        }
      case "*":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .multiply(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .multiply(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }
      case "distinct":
        if (!operands.isEmpty()) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).distinct(numeralOperands);
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).distinct(integerOperands);
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes at least one numeral operand as input. ");
        }
      case ">":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .greaterThan(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .greaterThan(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }
      case ">=":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .greaterOrEquals(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .greaterOrEquals(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }
      case "<":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .lessThan(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .lessThan(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }
      case "<=":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .lessOrEquals(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .lessOrEquals(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of numeral type");
          }
        } else {
          throw new ParserException(operator + " takes two numeral operands as input. ");
        }

      case "to_int":
        if (operands.size() == 1) {
          try {
            List<NumeralFormula> numeralOperands =
                operands.stream().map(e -> (NumeralFormula) e).collect(Collectors.toList());
            return Objects.requireNonNull(rmgr).floor(numeralOperands.get(0));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of real type");
          }
        } else {
          throw new ParserException(operator + " takes one real operands as input. ");
        }

      case "bvneg":
        // BitVec operators
        if (operands.size() != 1) {
          throw new ParserException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).negate((BitvectorFormula) operands.get(0));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvadd":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .add((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsub":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .subtract((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsdiv":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .divide(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvudiv":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .divide(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsrem":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .modulo(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvurem":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .modulo(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvmul":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .multiply((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsgt":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .greaterThan(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvugt":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .greaterThan(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsge":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .greaterOrEquals(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvuge":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .greaterOrEquals(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvslt":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .lessThan(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvult":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .lessThan(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsle":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .lessOrEquals(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvule":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .lessOrEquals(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvnot":
        if (operands.size() != 1) {
          throw new ParserException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).not((BitvectorFormula) operands.get(0));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvand":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .and((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvor":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .or((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvxor":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .xor((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvashr":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .shiftRight(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvlshr":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .shiftRight(
                    (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvshl":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .shiftLeft((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "concat":
        if (operands.size() != 2) {
          throw new ParserException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .concat((BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "extract":
        if (operands.size() == 1) {
          if (Objects.requireNonNull(operators).size() == 3
              && isInteger(operators.get(2))
              && isInteger(operators.get(1))) {
            int right = Integer.parseInt(operators.get(2));
            int left = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr)
                  .extract((BitvectorFormula) operands.get(0), left, right);
            } catch (Exception e) {
              throw new ParserException(
                  "Operands for " + operator + " need to be of bitvector type");
            }
          } else {
            throw new ParserException(
                operator + " takes one bitvector and two integers as input. ");
          }
        } else {
          throw new ParserException(
              operator + " takes one bitvector and two integers as " + "input.");
        }
      case "zero_extend":
        if (operands.size() == 1) {
          if (Objects.requireNonNull(operators).size() == 2 && isInteger(operators.get(1))) {
            int extension = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr)
                  .extend((BitvectorFormula) operands.get(0), extension, false);
            } catch (Exception e) {
              throw new ParserException(
                  "Operands for " + operator + " need to be of bitvector type");
            }
          } else {
            throw new ParserException(operator + " takes one bitvector and one integer as input. ");
          }
        } else {
          throw new ParserException(operator + " takes one bitvector and one integer as input.");
        }
      case "sign_extend":
        if (operands.size() == 1) {
          if (Objects.requireNonNull(operators).size() == 2 && isInteger(operators.get(1))) {
            int extension = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr)
                  .extend((BitvectorFormula) operands.get(0), extension, true);
            } catch (Exception e) {
              throw new ParserException(
                  "Operands for " + operator + " need to be of bitvector type");
            }
          } else {
            throw new ParserException(operator + " takes one bitvector and one integer as input. ");
          }
        } else {
          throw new ParserException(operator + " takes one bitvector and one integer as input.");
        }
      case "bv2int":
        if (operands.size() != 1) {
          throw new ParserException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .toIntegerFormula((BitvectorFormula) operands.get(0), false);
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "int2bv":
      case "rotate_left":
      case "rotate_right":
      case "repeat":
        throw new ParserException(operator + " is not available in JavaSMT");

      case "select":
        // array operators
        if (operands.size() == 2) {
          try {
            return Objects.requireNonNull(amgr)
                .select((ArrayFormula<Formula, Formula>) operands.get(0), operands.get(1));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of Array type");
          }
        } else {
          throw new ParserException(operator + " takes one array and one index as input. ");
        }
      case "store":
        if (operands.size() == 3) {
          try {
            return Objects.requireNonNull(amgr)
                .store(
                    (ArrayFormula<Formula, Formula>) operands.get(0),
                    operands.get(1),
                    operands.get(2));
          } catch (Exception e) {
            throw new ParserException("Operands for " + operator + " need to be of Array type");
          }
        } else {
          throw new ParserException(operator + " takes one array and one index as input. ");
        }
      case "const":
        // TODO I believe JavaSMT now supports const arrays?
        if (isModel) {
          variables.put(
              "temp",
              new ParserFormula(
                  Objects.requireNonNull(amgr)
                      .makeArray(
                          "(as const (Array "
                              + getArrayStrings(
                                  ((FormulaType.ArrayFormulaType<?, ?>)
                                          Objects.requireNonNull(sort))
                                      .getIndexType())
                              + " "
                              + getArrayStrings(
                                  ((FormulaType.ArrayFormulaType<?, ?>) sort).getElementType())
                              + ") "
                              + operands.get(0)
                              + ")",
                          (FormulaType.ArrayFormulaType<?, ?>) sort)));
          return variables.get("temp").javaSmt;
        } else {
          throw new ParserException("\"as const\" is not supported by JavaSMT");
        }
        case "fp.abs":
        if (operands.size() == 1) {
          return fpmgr.abs((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.abs requires exactly one "
              + "FloatingPointFormula operand.");
        }
        case "fp.neg":
        if (operands.size() == 1) {
          return fpmgr.negate((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.neg requires exactly one "
              + "FloatingPointFormula operand.");
        }
        case "fp.add":
        if (operands.size() == 3) {
          return fpmgr.add((FloatingPointFormula) operands.get(1),
              (FloatingPointFormula) operands.get(2),
              parseRoundingModesToJavaSMTFormat(operands.get(0).toString()));
        } else {
          throw new ParserException("fp.add requires a rounding mode and exactly two "
              + "FloatingPointFormula operands.");
        }
        case "fp.sub":
        if (operands.size() == 3) {
          return fpmgr.subtract((FloatingPointFormula) operands.get(1),
              (FloatingPointFormula) operands.get(2),
              parseRoundingModesToJavaSMTFormat(operands.get(0).toString()));
        } else {
          throw new ParserException("fp.sub requires a rounding mode and exactly two "
              + "FloatingPointFormula operands.");
        }
        case "fp.mul":
          if (operands.size() == 3) {
            return fpmgr.multiply((FloatingPointFormula) operands.get(1),
                (FloatingPointFormula) operands.get(2),
                parseRoundingModesToJavaSMTFormat(operands.get(0).toString()));
          } else {
            throw new ParserException("fp.mul requires a rounding mode and exactly two "
                + "FloatingPointFormula operands.");
          }
      case "fp.div":
        if (operands.size() == 3) {
          return fpmgr.divide((FloatingPointFormula) operands.get(1),
              (FloatingPointFormula) operands.get(2),
              parseRoundingModesToJavaSMTFormat(operands.get(0).toString()));
        } else {
          throw new ParserException("fp.div requires a rounding mode and exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.fma":
        //TODO: Seems to not be supported yet, but can be implemented
          throw new ParserException("fp.fma isn't supported by JavaSMT");
      case "fp.sqrt":
      if (operands.size() == 2) {
      return fpmgr.sqrt((FloatingPointFormula) operands.get(1),
          parseRoundingModesToJavaSMTFormat(operands.get(0).toString()));
      } else {
      throw new ParserException("fp.sqrt requires a rounding mode and exactly one "
          + "FloatingPointFormula operand.");
       }
      case "fp.rem":
          throw new ParserException("fp.rem is not suuported by JavaSMT");
      case "fp.roundToIntegral":
        throw new ParserException("fp.roundToIntegral is not supported by JavaSMT");
      case "fp.min" :
        if (operands.size() == 2) {
          return fpmgr.min((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.min requires exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.max" :
        if (operands.size() == 2) {
          return fpmgr.max((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.max requires exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.leq":
        if (operands.size() == 2) {
          return fpmgr.lessOrEquals((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.leq requires exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.lt":
        if (operands.size() == 2) {
          return fpmgr.lessThan((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.lt requires exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.geq":
        if (operands.size() == 2) {
          return fpmgr.greaterOrEquals((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.geq requires exactly two "
              + "FloatingPointFormula operands.");
        }
        case "fp.gt":
          if (operands.size() == 2) {
            return fpmgr.greaterThan((FloatingPointFormula) operands.get(0),
                (FloatingPointFormula) operands.get(1));
          } else {
            throw new ParserException("fp.gt requires exactly two "
                + "FloatingPointFormula operands.");
          }
      case "fp.eq":
        if (operands.size() == 2) {
          return fpmgr.equalWithFPSemantics((FloatingPointFormula) operands.get(0),
              (FloatingPointFormula) operands.get(1));
        } else {
          throw new ParserException("fp.eq requires exactly two "
              + "FloatingPointFormula operands.");
        }
      case "fp.isNormal":
        if (operands.size() == 1) {
          return fpmgr.isNormal((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.isNormal requires exactly one "
              + "FloatingPointFormula operand.");
        }
      case "fp.isSubnormal":
        if (operands.size() == 1) {
          return fpmgr.isSubnormal((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.isSubnormal requires exactly one "
              + "FloatingPointFormula operand.");
        }
      case "fp.isZero":
        if (operands.size() == 1) {
          return fpmgr.isZero((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.isZero requires exactly one "
              + "FloatingPointFormula operand.");
        }
      case "fp.isInfinity":
        if (operands.size() == 1) {
          return fpmgr.isInfinity((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.isZero requires exactly one "
              + "FloatingPointFormula operand.");
        }
      case "fp.isNegative":
        if (operands.size() == 1) {
          return fpmgr.isNegative((FloatingPointFormula) operands.get(0));
        } else {
          throw new ParserException("fp.isNegative requires exactly one "
              + "FloatingPointFormula operand.");
        }
      case "fp.isPositive":
        throw new ParserException("fp.isPositive is not supported by JavaSMT");
      case "UF":
        // UF
        try {
          return umgr.callUF(
              (FunctionDeclaration<? extends Formula>) Objects.requireNonNull(ufOperator),
              operands);
        } catch (Exception e) {
          throw new ParserException(operator + " takes one array and one index as input. ");
        }
      case "=":
        // overloaded operators
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof ArrayFormula)) {
              return Objects.requireNonNull(amgr)
                  .equivalence(
                      (ArrayFormula<Formula, Formula>) operands.get(0),
                      (ArrayFormula<Formula, Formula>) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              // if (operands.stream().anyMatch(c -> variables.containsKey(c)))
              return Objects.requireNonNull(rmgr)
                  .equal((NumeralFormula) operands.get(0), (NumeralFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof IntegerFormula)) {
              return Objects.requireNonNull(imgr)
                  .equal((IntegerFormula) operands.get(0), (IntegerFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof BooleanFormula)) {
              return bmgr.equivalence(
                  (BooleanFormula) operands.get(0), (BooleanFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof BitvectorFormula)) {
              BooleanFormula result =
                  Objects.requireNonNull(bimgr)
                      .equal(
                          (BitvectorFormula) operands.get(0), (BitvectorFormula) operands.get(1));
              return result;
            } else {
              throw new ParserException(
                  "Operands for " + operator + " need to be of the same type" + operands);
            }

          } catch (Exception e) {
            throw new ParserException(
                "Operands for " + operator + " need to be of the same type" + operands);
          }
        } else {
          throw new ParserException(operator + " takes two equal types of operands as input. ");
        }
      default:
        throw new ParserException("Operator " + operator + " is not supported for operands type.");
    }
  }

  @Override
  public Object visitTerm_let(Term_letContext ctx) {
    for (int i = 0; i < ctx.var_binding().size(); i++) {
      visit(ctx.var_binding(i));
    }
    Formula formula = (Formula) visit(ctx.term());
    for (int j = 0; j < ctx.var_binding().size(); j++) {
      letVariables.remove(ctx.var_binding(j).symbol().getText());
    }
    return formula;
  }

  @Override
  public Object visitTerm_forall(Term_forallContext ctx) {
    throw new ParserException("Parser does not support Quantifiers");
  }

  @Override
  public Object visitTerm_exists(Term_existsContext ctx) {
    throw new ParserException("Parser does not support Quantifiers");
  }

  @Override
  public Object visitTerm_exclam(Term_exclamContext ctx) {
    throw new ParserException("Parser does not support Attributed Expressions");
  }

  @Override
  public Object visitFunction_def(Function_defContext ctx) {
    String variable = replaceReservedChars(ctx.symbol().getText());

    List<FormulaType<?>> javaSorts;
    List<Formula> inputParams = new ArrayList<>();
    if (!ctx.sorted_var().isEmpty()) {
      for (int i = 0; i < ctx.sorted_var().size(); i++) {
        String name = ctx.sorted_var(i).symbol().getText();
        FormulaType<?> sort = (FormulaType<?>) visit(ctx.sorted_var(i).sort());
        Formula temp = mapKey(sort, name);
        variables.put(name, new ParserFormula(temp));
        inputParams.add(temp);
      }
    }
    javaSorts = inputParams.stream().map(fmgr::getFormulaType).collect(Collectors.toList());

    FormulaType<?> returnTypes = (FormulaType<?>) visit(ctx.sort());

    Formula key;
    Formula input = (Formula) visit(ctx.term());
    if (!inputParams.isEmpty()) {
      ParserFormula temp = new ParserFormula(umgr.declareUF(variable, returnTypes, javaSorts));
      temp.setType("UF");
      temp.setReturnType(returnTypes);
      temp.setInputParams(javaSorts);
      variables.put(variable, temp);
      key =
          umgr.callUF(
              (FunctionDeclaration<? extends Formula>) variables.get(variable).javaSmt,
              inputParams);
    } else {
      key = mapKey(returnTypes, variable);
    }

    Formula value = input;
    variables.put(variable, new ParserFormula(input));

    String keyString = replaceReplacedChars(key.toString());
    String valueString = value.toString();
    // TODO Does this add function definitions to the model?
    //  UPDATE Actually this is used together with `visitResp_get_model` to parse the model returned
    //         by the solver after (get-model) is used.
    if (isModel) {
      Model.ValueAssignment assignment =
          new ValueAssignment(
              key, value, mapEquivalence(key, value), keyString, valueString, new ArrayList<>());
      assignments.add(assignment);
    }
    return visitChildren(ctx);
  }

  @Override
  public Object visitCmd_assert(Cmd_assertContext ctx) {
    Object result = visitChildren(ctx);
    try {
      constraints.add((BooleanFormula) result);
      return result;
    } catch (Exception pE) {
      throw new ParserException("constraints need to be of Boolean type");
    }
  }

  @Override
  public Object visitCmd_declareConst(Cmd_declareConstContext ctx) {
    String variableSymbol = ctx.symbol().getText();
    FormulaType<?> sort = (FormulaType<?>) visit(ctx.sort());

    if (sort.isBooleanType()) {
      variables.put(variableSymbol, new ParserFormula(bmgr.makeVariable(variableSymbol)));
    } else if (sort.isIntegerType()) {
      variables.put(
          variableSymbol,
          new ParserFormula(Objects.requireNonNull(imgr).makeVariable(variableSymbol)));
    } else if (sort.isRationalType()) {
      variables.put(
          variableSymbol,
          new ParserFormula(Objects.requireNonNull(rmgr).makeVariable(variableSymbol)));
    } else if (sort.isBitvectorType()) {
      variables.put(
          variableSymbol,
          new ParserFormula(
              Objects.requireNonNull(bimgr)
                  .makeVariable(((FormulaType.BitvectorType) sort).getSize(), variableSymbol)));
    } else if(sort.isFloatingPointType()){
      variables.put(
          variableSymbol,
          new ParserFormula(Objects.requireNonNull(fpmgr).makeVariable(variableSymbol,
              (FormulaType.FloatingPointType) sort)) //TODO check if the last cast is correct.
      );
  }


else if (sort.isArrayType()) {
      variables.put(
          variableSymbol,
          new ParserFormula(
              Objects.requireNonNull(amgr)
                  .makeArray(
                      variableSymbol,
                      ((FormulaType.ArrayFormulaType<?, ?>) sort).getIndexType(),
                      ((FormulaType.ArrayFormulaType<?, ?>) sort).getElementType())));
    }
    return visitChildren(ctx);
  }

  /**
   * maps FormulaType to the corresponding SMT-LIB2 sort for the String representation of the model.
   *
   * @param type FormulaType that needs to be translated to SMT-LIB2
   * @return String representation of FormulaType in SMT-LIB2
   */
  public static String getArrayStrings(FormulaType<?> type) {

    if (type.isBooleanType()) {
      return "Bool";
    } else if (type.isIntegerType()) {
      return "Int";
    } else if (type.isRationalType()) {
      return "Real";
    }
    /*
    else if (type.isFloatingPointType()){
    return "(_ FloatingPoint ";
    }
     */
    else if (type.isBitvectorType()) {
      return "(_ BitVec " + ((BitvectorType) type).getSize() + ")";
    } else if (type.isArrayType()) {
      return "(Array "
          + getArrayStrings(((FormulaType.ArrayFormulaType<?, ?>) type).getIndexType())
          + " "
          + getArrayStrings(((FormulaType.ArrayFormulaType<?, ?>) type).getElementType());
    } else {
      throw new ParserException(type + " is not a known Sort.");
    }
  }

  /**
   * creates a Formula object to use as the key in ValueAssignments for model from the given
   * FormulaType.
   *
   * @param sorts FormulaType of the value in ValueAssignments
   * @param variable String representation of the key in ValueAssignments
   * @return Formula matching the given FormulaType 'sorts'
   */
  public Formula mapKey(FormulaType<?> sorts, String variable) {

    if (sorts.isBooleanType()) {
      return bmgr.makeVariable(variable);
    } else if (sorts.isIntegerType()) {
      return Objects.requireNonNull(imgr).makeVariable(variable);
    } else if (sorts.isRationalType()) {
      return Objects.requireNonNull(rmgr).makeVariable(variable);
    } else if (sorts.isBitvectorType()) {
      return Objects.requireNonNull(bimgr)
          .makeVariable(((FormulaType.BitvectorType) sorts).getSize(), variable);
    } else if (sorts.isArrayType()) {
      return Objects.requireNonNull(amgr)
          .makeArray(
              variable,
              ((FormulaType.ArrayFormulaType<?, ?>) sorts).getIndexType(),
              ((FormulaType.ArrayFormulaType<?, ?>) sorts).getElementType());
    } else {
      throw new ParserException(sorts + " is not of a known Sort.");
    }
  }

  /**
   * Assembles a BooleanFormula for the ValueAssignment field 'formula' by applying
   * BooleanFormulaManager.equivalence() to key Formula and value Formula.
   *
   * @param key Variable name as Formula
   * @param value Variable value as Formula
   * @return Equivalence of key and value
   */
  public BooleanFormula mapEquivalence(Formula key, Formula value) {
    if (key instanceof BooleanFormula) {
      return bmgr.equivalence((BooleanFormula) key, (BooleanFormula) value);
    } else if (key instanceof IntegerFormula) {
      return Objects.requireNonNull(imgr).equal((IntegerFormula) key, (IntegerFormula) value);
    } else if (key instanceof RationalFormula) {
      return Objects.requireNonNull(rmgr).equal((RationalFormula) key, (RationalFormula) value);
    } else if (key instanceof BitvectorFormula) {
      return Objects.requireNonNull(bimgr).equal((BitvectorFormula) key, (BitvectorFormula) value);
    } else if (key instanceof ArrayFormula) {
      return Objects.requireNonNull(amgr)
          .equivalence(
              (ArrayFormula<Formula, Formula>) key, (ArrayFormula<Formula, Formula>) value);
    } else {
      throw new ParserException(key + " is not a valid Sort");
    }
  }

  /**
   * Checks if String contains forbidden characters and temporarily replaces them, can be undone
   * with 'replaceReplacedChars()'.
   *
   * @param variable String that is checked and modified if necessary
   * @return String with no forbidden characters
   */
  // TODO This won't work for something like "|PIPE|"
  //  But, do we need to replace the symbols anyway? Maybe we just remove the "|"s?
  public String replaceReservedChars(String variable) {
    if (variable.startsWith("|")) {
      return variable.replaceAll("\\|", "PIPE");
    } else if (variable.contains("\\")) {
      return variable.replaceAll("\\\\", "BACKSLASH");
    } else {
      return variable;
    }
  }

  /**
   * Reverses 'replaceReservedChars'.
   *
   * @param variable String that is checked for necessary char replacements
   * @return modified String
   */
  public String replaceReplacedChars(String variable) {
    if (variable.contains("PIPE")) {
      return variable.replaceAll("PIPE", "|");
    } else if (variable.contains("BACKSLASH")) {
      return variable.replaceAll("BACKSLASH", "\\");
    } else {
      return variable;
    }
  }

  @Override
  public Object visitCmd_declareFun(Cmd_declareFunContext ctx) {
    String variable = replaceReservedChars(ctx.symbol().getText());

    FormulaType<?> returnType = (FormulaType<?>) visit(ctx.sort(ctx.sort().size() - 1));

    List<FormulaType<?>> inputParams = new ArrayList<>();
    if (ctx.sort().size() > 1) {
      for (int i = 0; i < ctx.sort().size() - 1; i++) {
        inputParams.add((FormulaType<?>) visit(ctx.sort(i)));
      }
    }
    //TODO: ONLY IF DECL_FUN IS NOT A FLOATING POINT RETURN AN UF OBJECT.IF IT IS A FLOATING
    // POINT WE will return something like: return new ParselFormula(fpmgr.blablabla))

    ParserFormula temp = new ParserFormula(umgr.declareUF(variable, returnType, inputParams));
    temp.setType("UF");
    temp.setReturnType(returnType);
    temp.setInputParams(inputParams);
    variables.put(variable, temp);

    return visitChildren(ctx);
  }

  /**
   * Method for parsing a String to the matching Rounding Mode from the FloatingPointRoundMode
   * Interface
   * @param roundingModeInSMTLIB SMTLIB2 String
   * @return matching FloatingPointRoundingMode
   */
  public static FloatingPointRoundingMode parseRoundingModesToJavaSMTFormat(String roundingModeInSMTLIB){
    if(roundingModeInSMTLIB.equals("RNE") || roundingModeInSMTLIB.equals("roundNearestTiesToEven")){
      return FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;
    }
    if(roundingModeInSMTLIB.equals("RNA") || roundingModeInSMTLIB.equals("roundNearestTiesToAway")){
      return FloatingPointRoundingMode.NEAREST_TIES_AWAY;
    }
    if(roundingModeInSMTLIB.equals("RTP") || roundingModeInSMTLIB.equals("roundTowardPositive")){
      return FloatingPointRoundingMode.TOWARD_POSITIVE;
    }
    if(roundingModeInSMTLIB.equals("RTN") || roundingModeInSMTLIB.equals("roundTowardNegative")){
      return FloatingPointRoundingMode.TOWARD_NEGATIVE;
    }
    if(roundingModeInSMTLIB.equals("RTZ") || roundingModeInSMTLIB.equals("roundTowardZero")){
      return FloatingPointRoundingMode.TOWARD_ZERO;
    }
    throw new ParserException("Rounding Mode does not exist.");
  }

  @Override
  public Object visitCmd_pop(Cmd_popContext ctx) {
    throw new ParserException("Parser does not support \"pop\"");
  }

  @Override
  public Object visitCmd_push(Cmd_pushContext ctx) {
    throw new ParserException("Parser does not support \"push\"");
  }

  @Override
  public Object visitDecl_sort(Decl_sortContext ctx) {
    throw new ParserException("JavaSMT does not support \"declare-sort\"");
  }

  @Override
  public Object visitResp_get_model(Resp_get_modelContext ctx) {
    isModel = true;
    return visitChildren(ctx);
  }
}
