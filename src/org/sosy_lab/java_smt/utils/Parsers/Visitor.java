package org.sosy_lab.java_smt.utils.Parsers;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;


@SuppressWarnings({"CheckReturnValue", "unchecked"})
public class Visitor extends smtlibv2BaseVisitor<Object> {

  HashMap<String, ParserFormula> variables = new HashMap<>();
  List<BooleanFormula> constraints = new ArrayList<>();
  private FormulaManager fmgr;
  private final BooleanFormulaManager bmgr;
  private final @Nullable IntegerFormulaManager imgr;
  private final @Nullable RationalFormulaManager rmgr;
  private final @Nullable BitvectorFormulaManager bimgr;
  private final @Nullable ArrayFormulaManager amgr;
  private final UFManager umgr;

  public HashMap<String, ParserFormula> getVariables() {
    return variables;
  }

  public List<BooleanFormula> getConstraints() {
    return constraints;
  }

  public Visitor(BooleanFormulaManager bmgr,
      @Nullable IntegerFormulaManager imgr,
      @Nullable RationalFormulaManager rmgr, @Nullable BitvectorFormulaManager bimgr,
      @Nullable ArrayFormulaManager amgr, UFManager umgr) {
    this.bmgr = bmgr;
    this.imgr = imgr;
    this.rmgr = rmgr;
    this.bimgr = bimgr;
    this.amgr = amgr;
    this.umgr = umgr;


  }

  @Override public Object visitStart_logic(smtlibv2Parser.Start_logicContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitStart_theory(smtlibv2Parser.Start_theoryContext ctx) { return visitChildren(ctx); }

  @Override public Object visitStart_script(smtlibv2Parser.Start_scriptContext ctx) {
    BooleanFormula constraint = bmgr.and(constraints);
    return visitChildren(ctx);
  }

  @Override public Object visitStart_gen_resp(smtlibv2Parser.Start_gen_respContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGeneralReservedWord(smtlibv2Parser.GeneralReservedWordContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSimp_pre_symb(smtlibv2Parser.Simp_pre_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSimp_undef_symb(smtlibv2Parser.Simp_undef_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitQuotedSymbol(smtlibv2Parser.QuotedSymbolContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPredefSymbol(smtlibv2Parser.PredefSymbolContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPredefKeyword(smtlibv2Parser.PredefKeywordContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSimpsymb(smtlibv2Parser.SimpsymbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitQuotsymb(smtlibv2Parser.QuotsymbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitNumeral(smtlibv2Parser.NumeralContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecimal(smtlibv2Parser.DecimalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitHexadecimal(smtlibv2Parser.HexadecimalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitBinary(smtlibv2Parser.BinaryContext ctx) { return visitChildren(ctx); }

  @Override public Object visitString(smtlibv2Parser.StringContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPre_key(smtlibv2Parser.Pre_keyContext ctx) { return visitChildren(ctx); }

  @Override public Object visitKey_simsymb(smtlibv2Parser.Key_simsymbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSpec_constant_num(smtlibv2Parser.Spec_constant_numContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSpec_constant_dec(smtlibv2Parser.Spec_constant_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSpec_constant_hex(smtlibv2Parser.Spec_constant_hexContext ctx) { return visitChildren(ctx); }

  @Override public String visitSpec_constant_bin(smtlibv2Parser.Spec_constant_binContext ctx) {
    String binary = ctx.getText();
    return binary;
  }

  @Override public Object visitSpec_constant_string(smtlibv2Parser.Spec_constant_stringContext ctx) { return visitChildren(ctx); }

  @Override public Object visitS_expr_spec(smtlibv2Parser.S_expr_specContext ctx) { return visitChildren(ctx); }

  @Override public Object visitS_expr_symb(smtlibv2Parser.S_expr_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitS_expr_key(smtlibv2Parser.S_expr_keyContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMulti_s_expr(smtlibv2Parser.Multi_s_exprContext ctx) { return visitChildren(ctx); }

  @Override public Object visitIdx_num(smtlibv2Parser.Idx_numContext ctx) { return visitChildren(ctx); }

  @Override public Object visitIdx_symb(smtlibv2Parser.Idx_symbContext ctx) { return visitChildren(ctx); }

  @Override public List<String> visitId_symb(smtlibv2Parser.Id_symbContext ctx) {
    List<String> sort = new ArrayList<>();
    sort.add(ctx.getText());
    return sort;
  }

  @Override public List<String> visitId_symb_idx(smtlibv2Parser.Id_symb_idxContext ctx) {
    List<String> sort = new ArrayList<>();
    sort.add(ctx.symbol().getText());
    for (int i = 0; i < ctx.index().size(); i++) {
      sort.add(ctx.index(i).getText());
    }
    return sort;
  }

  @Override public Object visitAttr_spec(smtlibv2Parser.Attr_specContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAttr_symb(smtlibv2Parser.Attr_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAttr_s_expr(smtlibv2Parser.Attr_s_exprContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAttr_key(smtlibv2Parser.Attr_keyContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAttr_key_attr(smtlibv2Parser.Attr_key_attrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSort_id(smtlibv2Parser.Sort_idContext ctx) {
    return visitChildren(ctx);
  }

  @Override public List<String> visitMultisort(smtlibv2Parser.MultisortContext ctx) {
    List<String> sorts = new ArrayList<>();
    sorts.add(ctx.identifier().getText());
    for (int i = 0; i < ctx.sort().size(); i++) {
      sorts.add(ctx.sort(i).getText());
    }
    return sorts;
  }

  @Override public Object visitQual_id(smtlibv2Parser.Qual_idContext ctx) { return visitChildren(ctx); }

  @Override public Object visitQual_id_sort(smtlibv2Parser.Qual_id_sortContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitVar_binding(smtlibv2Parser.Var_bindingContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSorted_var(smtlibv2Parser.Sorted_varContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPattern_symb(smtlibv2Parser.Pattern_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPattern_multisymb(smtlibv2Parser.Pattern_multisymbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMatch_case(smtlibv2Parser.Match_caseContext ctx) { return visitChildren(ctx); }


  public static boolean isInteger(String strNum) {
    try {
      Integer d = Integer.parseInt(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isFloat(String strNum) {
    try {
      Float d = Float.parseFloat(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }
  public static boolean isDouble(String strNum) {
    try {
      double d = Double.parseDouble(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isLong(String strNum) {
    try {
      Long d = Long.parseLong(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static boolean isBigInteger(String strNum) {
    try {
      BigInteger d = new BigInteger(strNum);
    } catch (NumberFormatException nfe) {
      return false;
    }
    return true;
  }

  public static String getNumericType(String strNum) {
    if (isInteger(strNum)) {
      return "Integer";
    } else if (isLong(strNum)) {
      return "Long";
    } else if (isDouble(strNum)) {
      return "Double";
    } else if (isBigInteger(strNum)) {
      return "BigInteger";
    } else if (isFloat(strNum)) {
      return "Float";
    } else {
      return "other";
    }
  }

  @Override public Object visitTerm_spec_const(smtlibv2Parser.Term_spec_constContext ctx)
      throws IOException {
    String operand = ctx.getText();
    if (variables.containsKey(operand)) {
      return variables.get(operand).javaSmt;
    } else if (getNumericType(operand).equals("Integer") | getNumericType(operand).equals("Long")) {
      variables.put(operand, new ParserFormula("Int", Objects.requireNonNull(imgr).makeNumber(operand)));
      return variables.get(operand).javaSmt;
    } else if (getNumericType(operand).equals("Double") | getNumericType(operand).equals("Float")) {
      variables.put(operand, new ParserFormula("Real", Objects.requireNonNull(rmgr).makeNumber(operand)));
      return variables.get(operand).javaSmt;
    } else if (operand.startsWith("#b")) {
      String binVal = operand.split("b")[1];
      int index = binVal.length();
      int value = Integer.parseInt(binVal, 2);
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    } else if (operand.startsWith("#x")) {
      String hexVal = operand.split("x")[1];
      int index = (hexVal.length()*4);
      BigInteger value = new BigInteger(hexVal, 16);
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    } else {
      throw new IOException("Operand " + operand + " is unknown.");
    }
  }

  @Override public Object visitTerm_qual_id(smtlibv2Parser.Term_qual_idContext ctx)
      throws IOException {
    // TODO: Error handling

    String operand = ctx.getText();
    if (operand.startsWith("|")) {
      operand = operand.split("\\|")[1];
      operand = operand.split("\\|")[0];
    }
    List<String> bitVec = (List<String>) visitChildren(ctx);
    if (variables.containsKey(operand)) {
      if (variables.get(operand).type.equals("UF") && variables.get(operand).inputParams.isEmpty()) {
        return umgr.callUF((FunctionDeclaration) variables.get(operand).javaSmt, new ArrayList<>());
      }
      return variables.get(operand).javaSmt;
    } else if (operand.equals("false")) {
      variables.put(operand, new ParserFormula("Bool", bmgr.makeFalse()));
      return variables.get(operand).javaSmt;
    } else if (operand.equals("true")) {
      variables.put(operand, new ParserFormula("Bool", bmgr.makeTrue()));
      return variables.get(operand).javaSmt;
    } else if (!bitVec.isEmpty()) {
      BigInteger value = new BigInteger(bitVec.get(0).split("v")[1]);
      int index = Integer.parseInt(bitVec.get(1));
      return Objects.requireNonNull(bimgr).makeBitvector(index, value);
    } else {
      throw new IOException("Operand " + operand + " is unknown.");
    }
  }

  public void getOperands(smtlibv2Parser.MultitermContext ctx,
                          List<Formula> operands) {

    for (int i = 0; i < ctx.term().size(); ++i) {
      Object operand = visit(ctx.term(i));
      // do not add multi term to list of operands
      if (operand != null) {
        operands.add((Formula) operand);
      }
    }
  }

  @Override public Object visitMultiterm(smtlibv2Parser.MultitermContext ctx) throws IOException {
    //String operator = ctx.qual_identifer().getText();
    List<String> operators = (List<String>) visit(ctx.qual_identifer());
    //String binary = (String) visit(ctx.b);
    String operator = operators.get(0);
    Object ufOperator = null;
    if (variables.containsKey(operator)) {
      ufOperator = variables.get(operator).javaSmt;
      operator = "UF";
    }

    List<Formula> operands = new ArrayList<>();
    getOperands(ctx, operands);

    switch (operator) {
      //boolean operators
      case "and":
        try {
          List<BooleanFormula> booleanOperands =
              operands.stream().map(e -> (BooleanFormula) e).collect(Collectors.toList());
          return bmgr.and(booleanOperands);
        } catch (Exception e) {
          throw new IOException("Operands for " + operator + " need to be of Boolean type");
        }
      case "or":
        try {
          List<BooleanFormula> booleanOperands =
              operands.stream().map(e -> (BooleanFormula) e).collect(Collectors.toList());
          return bmgr.or(booleanOperands);
        } catch (Exception e) {
          throw new IOException("Operands for " + operator + " need to be of Boolean type");
        }
      case "xor":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.xor((BooleanFormula) it.next(), (BooleanFormula) it.next());
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of Boolean type");
          }
        }
      case "not":
        if (operands.size() != 1) {
          throw new IOException(operator + " takes one boolean operand as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.not((BooleanFormula) it.next());
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of Boolean type");
          }
        }
      case "=>":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.implication((BooleanFormula) it.next(), (BooleanFormula) it.next());
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of Boolean type");
          }
        }
      case "ite":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two boolean operands as input.");
        } else {
          try {
            Iterator<Formula> it = operands.iterator();
            return bmgr.ifThenElse((BooleanFormula) it.next(), (BooleanFormula) it.next(),
                (BooleanFormula) it.next());
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of Boolean type");
          }
        }
        //numeral operators
      case "+":
        if (!operands.isEmpty()) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).sum(numeralOperands);
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).sum(integerOperands);
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes at least one numeral operand as input. ");
        }
      case "-":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).subtract(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).subtract(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else if (operands.size() == 1) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).negate(numeralOperands.get(0));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).negate(integerOperands.get(0));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes either one or two numeral operands as input. ");
        }
      case "div":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).divide(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).divide(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }
      case "mod":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              throw new IOException(operator + " is not available for Reals. ");
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).modulo(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of integer type");
          }
        } else {
          throw new IOException(operator + " takes two integer operands as input. ");
        }
      case "*":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).multiply(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).multiply(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }
      case "distinct":
        if (!operands.isEmpty()) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).distinct(numeralOperands);
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).distinct(integerOperands);
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes at least one numeral operand as input. ");
        }
      case ">":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .greaterOrEquals(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .greaterThan(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }
      case ">=":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .greaterOrEquals(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .greaterOrEquals(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }
      case "<":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr).lessThan(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr).lessThan(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }
      case "<=":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              List<NumeralFormula> numeralOperands =
                  operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(rmgr)
                  .lessOrEquals(numeralOperands.get(0), numeralOperands.get(1));
            } else {
              List<IntegerFormula> integerOperands =
                  operands.stream().map(e -> (IntegerFormula) e).collect(Collectors.toList());
              return Objects.requireNonNull(imgr)
                  .lessOrEquals(integerOperands.get(0), integerOperands.get(1));
            }
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of numeral type");
          }
        } else {
          throw new IOException(operator + " takes two numeral operands as input. ");
        }

      case "to_int":
        if (operands.size() == 1) {
          try {
            List<NumeralFormula> numeralOperands =
                operands.stream().map(e -> (RationalFormula) e).collect(Collectors.toList());
            return Objects.requireNonNull(rmgr).floor(numeralOperands.get(0));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of real type");
          }
        } else {
          throw new IOException(operator + " takes one real operands as input. ");
        }

        //BitVec operators
      case "bvneg":
        if (operands.size() != 1) {
          throw new IOException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).negate((BitvectorFormula) operands.get(0));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvadd":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).add((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + " need to be of bitvector type");
          }
        }
      case "bvsub":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).subtract((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvsdiv":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).divide((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvudiv":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).divide((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvsrem":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).modulo((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvurem":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).modulo((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvmul":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).multiply((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvsgt":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).greaterThan((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvugt":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).greaterThan((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvsge":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).greaterOrEquals((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvuge":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).greaterOrEquals((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvslt":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).lessThan((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvult":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).lessThan((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvsle":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).lessOrEquals((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvule":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).lessOrEquals((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvnot":
        if (operands.size() != 1) {
          throw new IOException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).not((BitvectorFormula) operands.get(0));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvand":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).and((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvor":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).or((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvxor":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).xor((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvashr":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).shiftRight((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), true);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvlshr":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).shiftRight((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "bvshl":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).shiftLeft((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "concat":
        if (operands.size() != 2) {
          throw new IOException(operator + " takes two bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr).concat((BitvectorFormula) operands.get(0),
                (BitvectorFormula) operands.get(1));
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "extract":
        if (operands.size() == 1) {
          if (operators.size() == 3 && isInteger(operators.get(2)) && isInteger(operators.get(1))) {
            int left = Integer.parseInt(operators.get(2));
            int right = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr).extract((BitvectorFormula) operands.get(0),
                  left, right);
            } catch (Exception e) {
              throw new IOException("Operands for " + operator + "need to be of bitvector type");
            }
          } else {
            throw new IOException(operator + " takes one bitvector and two integers as input. ");
          }
        }
      case "zero_extend":
        if (operands.size() == 1) {
          if (operators.size() == 2 && isInteger(operators.get(1))) {
            int extension = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr).extend((BitvectorFormula) operands.get(0),
                  extension, true);
            } catch (Exception e) {
              throw new IOException("Operands for " + operator + "need to be of bitvector type");
            }
          } else {
            throw new IOException(operator + " takes one bitvector and one integer as input. ");
          }
        }
      case "sign_extend":
        if (operands.size() == 1) {
          if (operators.size() == 2 && isInteger(operators.get(1))) {
            int extension = Integer.parseInt(operators.get(1));
            try {
              return Objects.requireNonNull(bimgr).extend((BitvectorFormula) operands.get(0),
                  extension, false);
            } catch (Exception e) {
              throw new IOException("Operands for " + operator + "need to be of bitvector type");
            }
          } else {
            throw new IOException(operator + " takes one bitvector and one integer as input. ");
          }
        }
      case "bv2int":
        if (operands.size() != 1) {
          throw new IOException(operator + " takes one bitvector operand as input.");
        } else {
          try {
            return Objects.requireNonNull(bimgr)
                .toIntegerFormula((BitvectorFormula) operands.get(0), false);
          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of bitvector type");
          }
        }
      case "int2bv":
      case "rotate_left":
      case "rotate_right":
      case "repeat":
        throw new IOException(operator + " is not available in JavaSMT");

        //array operators
      case "select":
        if (operands.size() == 2) {
          return Objects.requireNonNull(amgr).select((ArrayFormula<Formula, Formula>) operands.get(0),
              operands.get(1));
        } else {
          throw new IOException(operator + " takes one array and one index as input. ");
        }
      case "store":
        if (operands.size() == 3) {
          return Objects.requireNonNull(amgr)
              .store((ArrayFormula<Formula, Formula>) operands.get(0), operands.get(1), operands.get(2));
        } else {
          throw new IOException(operator + " takes one array and one index as input. ");
        }

        //UF
      case "UF":
        try {
          return umgr.callUF((FunctionDeclaration<? extends Formula>) Objects.requireNonNull(
              ufOperator), operands);
        } catch (Exception e) {
          throw new IOException(operator + " takes one array and one index as input. ");
        }

        //overloaded operators
      case "=":
        if (operands.size() == 2) {
          try {
            if (operands.stream().anyMatch(c -> c instanceof RationalFormula)) {
              return Objects.requireNonNull(rmgr).equal((NumeralFormula) operands.get(0),
                  (NumeralFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof IntegerFormula)) {
              return Objects.requireNonNull(imgr).equal((IntegerFormula) operands.get(0),
                  (IntegerFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof BooleanFormula)) {
              return bmgr.equivalence((BooleanFormula) operands.get(0),
                  (BooleanFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof BitvectorFormula)) {
              return Objects.requireNonNull(bimgr).equal((BitvectorFormula) operands.get(0),
                  (BitvectorFormula) operands.get(1));
            } else if (operands.stream().anyMatch(c -> c instanceof ArrayFormula)){
              return Objects.requireNonNull(amgr).equivalence((ArrayFormula<Formula, Formula>) operands.get(0),
                  (ArrayFormula<Formula, Formula>) operands.get(1));
            }

          } catch (Exception e) {
            throw new IOException("Operands for " + operator + "need to be of the same type");
          }
        } else {
          throw new IOException(operator + " takes two equal types of operands as input. ");
        }
          default:
            throw new IOException("Operator " + operator + " is not supported for operands type.");

    }
  }

  @Override public Object visitTerm_let(smtlibv2Parser.Term_letContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTerm_forall(smtlibv2Parser.Term_forallContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTerm_exists(smtlibv2Parser.Term_existsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTerm_match(smtlibv2Parser.Term_matchContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTerm_exclam(smtlibv2Parser.Term_exclamContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSort_symbol_decl(smtlibv2Parser.Sort_symbol_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMeta_spec_constant(smtlibv2Parser.Meta_spec_constantContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFun_symb_spec(smtlibv2Parser.Fun_symb_specContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFun_symb_meta(smtlibv2Parser.Fun_symb_metaContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFun_symb_id(smtlibv2Parser.Fun_symb_idContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPar_fun_symb(smtlibv2Parser.Par_fun_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPar_fun_multi_symb(smtlibv2Parser.Par_fun_multi_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_sort(smtlibv2Parser.Theory_sortContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_fun(smtlibv2Parser.Theory_funContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_sort_descr(smtlibv2Parser.Theory_sort_descrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_fun_descr(smtlibv2Parser.Theory_fun_descrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_def(smtlibv2Parser.Theory_defContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_val(smtlibv2Parser.Theory_valContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_notes(smtlibv2Parser.Theory_notesContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_attr(smtlibv2Parser.Theory_attrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitTheory_decl(smtlibv2Parser.Theory_declContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_theory(smtlibv2Parser.Logic_theoryContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_language(smtlibv2Parser.Logic_languageContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_ext(smtlibv2Parser.Logic_extContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_val(smtlibv2Parser.Logic_valContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_notes(smtlibv2Parser.Logic_notesContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic_attr(smtlibv2Parser.Logic_attrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitLogic(smtlibv2Parser.LogicContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSort_dec(smtlibv2Parser.Sort_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSelector_dec(smtlibv2Parser.Selector_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitConstructor_dec(smtlibv2Parser.Constructor_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitData_constr(smtlibv2Parser.Data_constrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitData_multisymb(smtlibv2Parser.Data_multisymbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFunction_dec(smtlibv2Parser.Function_decContext ctx) { return visitChildren(ctx); }

  @Override public Object visitFunction_def(smtlibv2Parser.Function_defContext ctx)
      throws IOException {
    String variable = ctx.symbol().getText();
    if (variable.startsWith("|")) {
      variable = variable.split("\\|")[1];
      variable = variable.split("\\|")[0];
    }
    List<String> declaration = new ArrayList<>();
    List<FormulaType<?>> javaSorts = new ArrayList<>();
    String returnType = ctx.getChild(ctx.getChildCount() - 1).getText();
    for (int i = 0; i < ctx.getChildCount(); i++) {
      declaration.add(ctx.getChild(i).getText());
    }
    String name;
    String sort;
      for (int i = 0; i < ctx.sorted_var().size(); i++) {
        name = ctx.sorted_var(i).symbol().getText();
        sort = ctx.sorted_var(i).sort().getText();
        variables.put(name, new ParserFormula(sort, mapSort(sort)));
      }
        String returnVal = ctx.sort().getText();
        Formula input = (Formula) visit(ctx.term());

        ParserFormula temp =
            new ParserFormula("UF", umgr.declareAndCallUF(variable, mapSort(returnVal), input));
        temp.setReturnType(mapSort(returnVal));
        //TODO: get rid of dummy
        List<FormulaType<?>> dummy = new ArrayList<>();
        dummy.add(FormulaType.IntegerType);
        temp.setInputParams(dummy);
        variables.put(variable, temp);

    return visitChildren(ctx);
  }

  @Override public Object visitProp_symb(smtlibv2Parser.Prop_symbContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProp_not(smtlibv2Parser.Prop_notContext ctx) { return visitChildren(ctx); }

  @Override public Object visitScript(smtlibv2Parser.ScriptContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_assert(smtlibv2Parser.Cmd_assertContext ctx) throws IOException {
    Object result = visitChildren(ctx);
    try {
      constraints.add((BooleanFormula) result);
      return result;
    } catch (Exception pE) {
      throw new IOException("constraints need to be of Boolean type");
    }
  }

  @Override public Object visitCmd_checkSat(smtlibv2Parser.Cmd_checkSatContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_checkSatAssuming(smtlibv2Parser.Cmd_checkSatAssumingContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCmd_declareConst(smtlibv2Parser.Cmd_declareConstContext ctx)
      throws IOException {
    String variable = ctx.symbol().getText();
    List<String> sorts = (List<String>) visit(ctx.sort());
    String sort = sorts.get(0);
    switch (sort) {
      case "Bool":
        variables.put(variable, new ParserFormula("Bool", bmgr.makeVariable(variable)));
        break;
      case "Int":
        variables.put((variable), new ParserFormula("Int", Objects.requireNonNull(imgr).makeVariable(variable)));
        break;
      case "Real":
        variables.put((variable), new ParserFormula("Real", Objects.requireNonNull(rmgr).makeVariable(variable)));
        break;
      case "BitVec":
        if (sorts.size() == 2) {
          String index = sorts.get(1);
          if (isInteger(index)) {
            variables.put(variable, new ParserFormula("BitVec", Objects.requireNonNull(bimgr).makeVariable(
                Integer.parseInt(index),
                variable)));
          } else {
            throw new IOException("BitVec declaration needs to be of form (_ BitVec Int)");
          }

        }
        break;
      case "Array":
        if (sorts.size() == 3) {
          String index = sorts.get(1);
          String elements = sorts.get(2);
          String bvSize = "";
          if (index.startsWith("(_BitVec")) {
            bvSize = index.split("_BitVec")[1];
            bvSize = bvSize.split("\\)")[0];
            index = "BitVec";
          }
          if (elements.startsWith("(_BitVec")) {
            bvSize = elements.split("_BitVec")[1];
            bvSize = bvSize.split("\\)")[0];
            elements = "BitVec";
          }
          switch (index) {
            case "Int": {
              FormulaType<IntegerFormula> idx = FormulaType.IntegerType;
              break;
            }
            case "Bool": {
              FormulaType<BooleanFormula> idx = FormulaType.BooleanType;
              break;
            }
            case "Real": {
              FormulaType<RationalFormula> idx = FormulaType.RationalType;
              break;
            }
            case "BitVec": {
              FormulaType<BitvectorFormula> idx =
                  FormulaType.BitvectorType.getBitvectorTypeWithSize(Integer.parseInt(bvSize));
              break;
            }
            default:
              throw new IOException(index + " is not a supported array index sort");
          }
          switch (elements) {
            case "Int": {
              FormulaType<IntegerFormula> elem = FormulaType.IntegerType;
              break;
            }
            case "Bool": {
              FormulaType<BooleanFormula> elem = FormulaType.BooleanType;
              break;
            }
            case "Real": {
              FormulaType<RationalFormula> elem = FormulaType.RationalType;
              break;
            }
            case "BitVec": {
              FormulaType<BitvectorFormula> elem =
                  FormulaType.BitvectorType.getBitvectorTypeWithSize(Integer.parseInt(bvSize));
              break;
            }
            default:
              throw new IOException(elements + " is not a supported array element sort");
          }
          variables.put((variable), new ParserFormula("Array", Objects.requireNonNull(amgr).makeArray(variable,
              FormulaType.IntegerType, FormulaType.IntegerType)));
        }
        break;
    }
    return visitChildren(ctx);
  }

  @Override public Object visitCmd_declareDatatype(smtlibv2Parser.Cmd_declareDatatypeContext ctx) {

    return visitChildren(ctx);
  }

  @Override public Object visitCmd_declareDatatypes(smtlibv2Parser.Cmd_declareDatatypesContext ctx) { return visitChildren(ctx); }

  public static FormulaType<?> mapSort(String sorts) throws IOException {
    String bvSize = "";
    if (sorts.startsWith("(_BitVec")) {
      bvSize = sorts.split("_BitVec")[1];
      bvSize = bvSize.split("\\)")[0];
      sorts = "BitVec";
    }

    switch (sorts) {
      case "Int":
        return FormulaType.IntegerType;
      case "Bool":
        return FormulaType.BooleanType;
      case "Real":
        return FormulaType.RationalType;
      case "BitVec":
        return FormulaType.BitvectorType.getBitvectorTypeWithSize(Integer.parseInt(bvSize));
      default:
        throw new IOException("JavaSMT supports only Int, Real, BitVec and Bool for UF.");
    }
    }

  @Override public Object visitCmd_declareFun(smtlibv2Parser.Cmd_declareFunContext ctx)
      throws IOException {
    String variable = ctx.symbol().getText();
    if (variable.startsWith("|")) {
      variable = variable.split("\\|")[1];
      variable = variable.split("\\|")[0];
    }
    List<String> declaration = new ArrayList<>();
    List<FormulaType<?>> javaSorts = new ArrayList<>();
    String returnType = ctx.getChild(ctx.getChildCount() - 1).getText();
    for (int i = 0; i < ctx.getChildCount(); i++) {
      declaration.add(ctx.getChild(i).getText());
    }

    List<String> inputParams = new ArrayList<>();
    if (ctx.getChildCount() > 4 && ! ctx.getChild(3).getText().equals(")")) {
      inputParams = declaration.subList(3, ctx.getChildCount() - 2);
      javaSorts = inputParams.stream().map(e -> {
        try {
          return mapSort(e);
        } catch (IOException pE) {
          throw new RuntimeException(pE);
        }
      }).collect(Collectors.toList());
    }

    ParserFormula temp = new ParserFormula("UF", umgr.declareUF(variable, mapSort(returnType),
        javaSorts));
    temp.setReturnType(mapSort(returnType));
    temp.setInputParams(javaSorts);
    variables.put(variable, temp);

    return visitChildren(ctx);
  }

  @Override public Object visitCmd_declareSort(smtlibv2Parser.Cmd_declareSortContext ctx) { return visitChildren(ctx); }

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

  @Override public Object visitAssert(smtlibv2Parser.AssertContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCheck(smtlibv2Parser.CheckContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCheck_assume(smtlibv2Parser.Check_assumeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecl_const(smtlibv2Parser.Decl_constContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecl_data(smtlibv2Parser.Decl_dataContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecl_datas(smtlibv2Parser.Decl_datasContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecl_fun(smtlibv2Parser.Decl_funContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDecl_sort(smtlibv2Parser.Decl_sortContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDef_fun(smtlibv2Parser.Def_funContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDef_fun_rec(smtlibv2Parser.Def_fun_recContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDef_funs_rec(smtlibv2Parser.Def_funs_recContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDef_sort(smtlibv2Parser.Def_sortContext ctx) { return visitChildren(ctx); }

  @Override public Object visitEcho(smtlibv2Parser.EchoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitExit(smtlibv2Parser.ExitContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assert(smtlibv2Parser.Get_assertContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assign(smtlibv2Parser.Get_assignContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_info(smtlibv2Parser.Get_infoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_model(smtlibv2Parser.Get_modelContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_option(smtlibv2Parser.Get_optionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_proof(smtlibv2Parser.Get_proofContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_assume(smtlibv2Parser.Get_unsat_assumeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_core(smtlibv2Parser.Get_unsat_coreContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_val(smtlibv2Parser.Get_valContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPop(smtlibv2Parser.PopContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPush(smtlibv2Parser.PushContext ctx) { return visitChildren(ctx); }

  @Override public Object visitReset(smtlibv2Parser.ResetContext ctx) { return visitChildren(ctx); }

  @Override public Object visitReset_assert(smtlibv2Parser.Reset_assertContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSetInfo(smtlibv2Parser.SetInfoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSet_logic(smtlibv2Parser.Set_logicContext ctx) { return visitChildren(ctx); }

  @Override public Object visitSet_option(smtlibv2Parser.Set_optionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitB_value(smtlibv2Parser.B_valueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitDiagnose(smtlibv2Parser.DiagnoseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGlobal(smtlibv2Parser.GlobalContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInteractive(smtlibv2Parser.InteractiveContext ctx) { return visitChildren(ctx); }

  @Override public Object visitPrint_succ(smtlibv2Parser.Print_succContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_assert(smtlibv2Parser.Prod_assertContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_assign(smtlibv2Parser.Prod_assignContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_mod(smtlibv2Parser.Prod_modContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_proofs(smtlibv2Parser.Prod_proofsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_unsat_assume(smtlibv2Parser.Prod_unsat_assumeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitProd_unsat_core(smtlibv2Parser.Prod_unsat_coreContext ctx) { return visitChildren(ctx); }

  @Override public Object visitRand_seed(smtlibv2Parser.Rand_seedContext ctx) { return visitChildren(ctx); }

  @Override public Object visitReg_out(smtlibv2Parser.Reg_outContext ctx) { return visitChildren(ctx); }

  @Override public Object visitRepro(smtlibv2Parser.ReproContext ctx) { return visitChildren(ctx); }

  @Override public Object visitVerbose(smtlibv2Parser.VerboseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitOpt_attr(smtlibv2Parser.Opt_attrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAll_stat(smtlibv2Parser.All_statContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAssert_stack(smtlibv2Parser.Assert_stackContext ctx) { return visitChildren(ctx); }

  @Override public Object visitAuthors(smtlibv2Parser.AuthorsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitError(smtlibv2Parser.ErrorContext ctx) { return visitChildren(ctx); }

  @Override public Object visitName(smtlibv2Parser.NameContext ctx) { return visitChildren(ctx); }

  @Override public Object visitR_unknown(smtlibv2Parser.R_unknownContext ctx) { return visitChildren(ctx); }

  @Override public Object visitVersion(smtlibv2Parser.VersionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_key(smtlibv2Parser.Info_keyContext ctx) { return visitChildren(ctx); }

  @Override public Object visitError_behaviour(smtlibv2Parser.Error_behaviourContext ctx) { return visitChildren(ctx); }

  @Override public Object visitMemout(smtlibv2Parser.MemoutContext ctx) { return visitChildren(ctx); }

  @Override public Object visitIncomp(smtlibv2Parser.IncompContext ctx) { return visitChildren(ctx); }

  @Override public Object visitR_unnown_s_expr(smtlibv2Parser.R_unnown_s_exprContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_def_fun(smtlibv2Parser.Resp_def_funContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_def_fun_rec(smtlibv2Parser.Resp_def_fun_recContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_def_funs_rec(smtlibv2Parser.Resp_def_funs_recContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_assert_stack(smtlibv2Parser.Info_assert_stackContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_authors(smtlibv2Parser.Info_authorsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_error(smtlibv2Parser.Info_errorContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_name(smtlibv2Parser.Info_nameContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_r_unknown(smtlibv2Parser.Info_r_unknownContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_version(smtlibv2Parser.Info_versionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitInfo_attr(smtlibv2Parser.Info_attrContext ctx) { return visitChildren(ctx); }

  @Override public Object visitValuation_pair(smtlibv2Parser.Valuation_pairContext ctx) { return visitChildren(ctx); }

  @Override public Object visitT_valuation_pair(smtlibv2Parser.T_valuation_pairContext ctx) { return visitChildren(ctx); }

  @Override public Object visitCheck_sat_response(smtlibv2Parser.Check_sat_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitEcho_response(smtlibv2Parser.Echo_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assertions_response(smtlibv2Parser.Get_assertions_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_assignment_response(smtlibv2Parser.Get_assignment_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_info_response(smtlibv2Parser.Get_info_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitRs_model(smtlibv2Parser.Rs_modelContext ctx) { return visitChildren(ctx); }

  @Override public Object visitModel_resp(smtlibv2Parser.Model_respContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_option_response(smtlibv2Parser.Get_option_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_proof_response(smtlibv2Parser.Get_proof_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_assump_response(smtlibv2Parser.Get_unsat_assump_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_unsat_core_response(smtlibv2Parser.Get_unsat_core_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitGet_value_response(smtlibv2Parser.Get_value_responseContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_check_sat(smtlibv2Parser.Resp_check_satContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_echo(smtlibv2Parser.Resp_echoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_get_assert(smtlibv2Parser.Resp_get_assertContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_gett_assign(smtlibv2Parser.Resp_gett_assignContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_get_info(smtlibv2Parser.Resp_get_infoContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_get_model(smtlibv2Parser.Resp_get_modelContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_option(smtlibv2Parser.Resp_optionContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_proof(smtlibv2Parser.Resp_proofContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_unsat_assume(smtlibv2Parser.Resp_unsat_assumeContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_unsat_core(smtlibv2Parser.Resp_unsat_coreContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_value(smtlibv2Parser.Resp_valueContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_success(smtlibv2Parser.Resp_successContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_spec_successs(smtlibv2Parser.Resp_spec_successsContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_unsupported(smtlibv2Parser.Resp_unsupportedContext ctx) { return visitChildren(ctx); }

  @Override public Object visitResp_error(smtlibv2Parser.Resp_errorContext ctx) { return visitChildren(ctx); }
}