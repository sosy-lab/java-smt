// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.io.File;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.Appenders.AbstractAppender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBooleanFormula;

final class BitwuzlaFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  BitwuzlaFormulaManager(
      BitwuzlaFormulaCreator pFormulaCreator,
      BitwuzlaUFManager pFunctionManager,
      BitwuzlaBooleanFormulaManager pBooleanManager,
      BitwuzlaBitvectorFormulaManager pBitvectorManager,
      BitwuzlaQuantifiedFormulaManager pQuantifierManager,
      BitwuzlaFloatingPointManager pFloatingPointManager,
      BitwuzlaArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        pFloatingPointManager,
        pQuantifierManager,
        pArrayManager,
        null,
        null,
        null);
  }

  /**
   * Parse a boolean formula given as a String in an SMTLIB file format. We expect exactly one
   * assertion to be contained in the query.
   *
   * <p>Example: <code>(declare-fun x () Int)(assert (= 0 x))</code>
   *
   * <p>It depends on the used SMT solver whether the given query must be self-contained and include
   * declarations for all used symbols or not, and also whether the query is allowed to contain
   * symbols with equal name, but different type/sort than existing symbols. The safest way is to
   * always declare all used symbols and to avoid conflicting types for them.
   *
   * <p>The behavior of the SMT solver is undefined if commands are provided in the SMTLIB-based
   * String that are different from declarations or an assertion, such as <code>push/pop</code> or
   * <code>set-info</code>. Most solvers just ignore those commands.
   *
   * <p>Variables that are defined, but not used in the assertion, might be ignored by the SMT
   * solver and they might not be available for later usage.
   *
   * @param s
   * @return A single formula from the assertion in the internal representation.
   * @throws IllegalArgumentException If the string cannot be parsed.
   */
  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    long options = bitwuzlaJNI.bitwuzla_options_new();

    // Needs to be formatted like a file. Example:
    //    String inpuString = "(set-logic QF_ABV)\r\n" + //
    //        "(set-option :produce-models true)\r\n" + //
    //        "(declare-const x (_ BitVec 8))\r\n" + //
    //        "(declare-const y (_ BitVec 8))\r\n" + //
    //        "(declare-fun f ((_ BitVec 8) (_ BitVec 4)) (_ BitVec 8))\r\n" + //
    //        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\r\n" + //
    //        "(assert\r\n" + //
    //        "    (distinct\r\n" + //
    //        "        ((_ extract 3 0) (bvsdiv x (_ bv2 8)))\r\n" + //
    //        "        ((_ extract 3 0) (bvashr y (_ bv1 8)))))\r\n" + //
    //        "(assert (= (f x ((_ extract 6 3) x)) y))\r\n" + //
    //        "(assert (= (select a x) y))\r\n" + //
    //        "(check-sat)\r\n" + //
    //        "(get-model)\r\n" + //
    //        "(get-value (x y f a (bvmul x x)))\r\n" + //
    //        "(exit)\r\n";


    long pInfile = bitwuzlaJNI.fopen("tempParserFile", "w+");


    _IO_FILE infile = new _IO_FILE(pInfile, true);

    bitwuzlaJNI.fputs(s, _IO_FILE.getCPtr(infile), infile);

    // Not sure why this needs to be done, but Bitwuzla can only access the file in r or r+ mode
    bitwuzlaJNI.fclose(_IO_FILE.getCPtr(infile), infile);
    pInfile = bitwuzlaJNI.fopen("tempParserFile", "r");
    infile = new _IO_FILE(pInfile, true);

    long parser =
        bitwuzlaJNI.bitwuzla_parser_new(options, "tempParserFile", _IO_FILE.getCPtr(infile), infile,
            "smt2");


    // Boolean must be false
    String err_msg = bitwuzlaJNI.bitwuzla_parser_parse(parser, false);
    assert (err_msg == null);

    long[] size = new long[1];
    long pAssertionArray =
        bitwuzlaJNI.bitwuzla_get_assertions(bitwuzlaJNI.bitwuzla_parser_get_bitwuzla(parser), size);

    if (size[0] > 1) {
      throw new IllegalArgumentException("Included more than one assertion in string for parsing.");
    }

    long assertion = bitwuzlaJNI.BitwuzlaTermArray_getitem(pAssertionArray, 0);

//    System.out.println("Assertions:");
//    System.out.print("{");
//    for (int i = 0; i < size[0]; ++i) {
//      System.out.println(bitwuzlaJNI.bitwuzla_term_to_string(
//          bitwuzlaJNI.BitwuzlaTermArray_getitem(assertions, i)));
//    }
//    System.out.print("}");

    // Deleting infile is probably safer than the C function. Can't do both.
    // bitwuzlaJNI.fclose(_IO_FILE.getCPtr(infile), infile);

    infile.delete();

    // File needs to be deleted from Java-side
    File toDelete = new File("tempParserFile");
    toDelete.delete();

    bitwuzlaJNI.bitwuzla_parser_delete(parser);
    bitwuzlaJNI.bitwuzla_options_delete(options);

    return super.getFormulaCreator().encapsulateBoolean(assertion);
  }

  @Override
  public Appender dumpFormula(Long t) {

    StringBuilder out = new StringBuilder();
    out.append(bitwuzlaJNI.bitwuzla_term_to_string(t));
    Appender result = Appenders.createAppender(out);

    return result;
  }

  static long getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }
}
