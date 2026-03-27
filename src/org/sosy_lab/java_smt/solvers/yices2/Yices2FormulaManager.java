// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.CharMatcher.inRange;

import com.google.common.base.CharMatcher;
import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;
import com.google.common.primitives.Ints;
import com.sri.yices.Constructor;
import com.sri.yices.Terms;
import com.sri.yices.Types;
import java.io.IOException;
import java.util.Locale;
import java.util.Map;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class Yices2FormulaManager extends AbstractFormulaManager<Integer, Integer, Long, Integer> {

  private static final CharMatcher LETTERS = inRange('a', 'z').or(inRange('A', 'Z'));
  private static final CharMatcher DIGITS = inRange('0', '9');
  private static final CharMatcher ADDITIONAL_CHARS = CharMatcher.anyOf("~!@$%^&*_-+=<>.?/");
  private static final CharMatcher VALID_CHARS =
      LETTERS.or(DIGITS).or(ADDITIONAL_CHARS).precomputed();

  @SuppressWarnings("checkstyle:parameternumber")
  Yices2FormulaManager(
      LogManager pLogger,
      Configuration pConfiguration,
      Yices2FormulaCreator pFormulaCreator,
      Yices2UFManager pFunctionManager,
      Yices2BooleanFormulaManager pBooleanManager,
      Yices2IntegerFormulaManager pIntegerManager,
      Yices2RationalFormulaManager pRationalManager,
      Yices2BitvectorFormulaManager pBitvectorManager,
      Yices2QuantifiedFormulaManager pQuantifiedFormulaManager,
      Yices2ArrayFormulaManager pArrayFormulaManager)
      throws InvalidConfigurationException {
    super(
        pLogger,
        pConfiguration,
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        null,
        pQuantifiedFormulaManager,
        pArrayFormulaManager,
        null,
        null,
        null);
  }

  static Integer getYicesTerm(Formula pT) {
    return ((Yices2Formula) pT).getTerm();
  }

  @Override
  protected Integer equalImpl(Integer pArg1, Integer pArgs) {
    return Terms.eq(pArg1, pArgs);
  }

  @Override
  protected Integer distinctImpl(Iterable<Integer> pArgs) {
    int[] array = Ints.toArray(ImmutableList.copyOf(pArgs));
    if (array.length < 2) {
      return Terms.mkTrue();
    } else {
      return Terms.distinct(array);
    }
  }

  @Override
  protected Integer parseImpl(String pSmtScript) throws IllegalArgumentException {
    // Yices uses its own input language and can't parse smt-lib2
    throw new UnsupportedOperationException();
  }

  /** Helper function to (pretty) print yices2 sorts. */
  private String getTypeRepr(int type) {
    if (Types.isBitvector(type)) {
      return "(_ BitVec " + Types.bvSize(type) + ")";
    }
    String typeRepr = Types.toString(type);
    return typeRepr.substring(0, 1).toUpperCase(Locale.getDefault()) + typeRepr.substring(1);
  }

  @Override
  public String dumpFormulaImpl(final Integer formula) throws IOException {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder out = new StringBuilder();
    Map<String, Formula> varsAndUFs =
        extractVariablesAndUFs(getFormulaCreator().encapsulateWithTypeOf(formula));
    for (Map.Entry<String, Formula> entry : varsAndUFs.entrySet()) {
      final int term = ((Yices2Formula) entry.getValue()).getTerm();
      final int type;
      if (Terms.constructor(term) == Constructor.APP_TERM) {
        // Is an UF. Correct type is carried by first child.
        type = Terms.typeOf(Terms.child(term, 0));
      } else {
        type = Terms.typeOf(term);
      }
      final int[] types;
      if (Types.numChildren(type) == 0) {
        types = new int[] {type};
      } else {
        types = Types.children(type); // adds children types and then return type
      }
      if (types.length > 0) {
        out.append("(declare-fun ");
        out.append(quote(entry.getKey()));
        out.append(" (");
        for (int i = 0; i < types.length - 1; i++) {
          out.append(getTypeRepr(types[i]));
          if (i + 1 < types.length - 1) {
            out.append(' ');
          }
        }
        out.append(") ");
        out.append(getTypeRepr(types[types.length - 1]));
        out.append(")\n");
      }
    }
    // TODO fold formula to avoid exp. overhead
    out.append("(assert ").append(Terms.toString(formula, 100000, 1)).append(")");

    return out.toString();
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (otherManager instanceof Yices2FormulaManager) {
      return formula;
    }
    return super.translateFrom(formula, otherManager);
  }

  /**
   * Quote symbols if required.
   *
   * <p>See http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf, Section 3.1.
   * "Symbols"
   */
  private static String quote(String str) {
    Preconditions.checkArgument(!Strings.isNullOrEmpty(str));
    Preconditions.checkArgument(CharMatcher.anyOf("|\\").matchesNoneOf(str));
    Preconditions.checkArgument(!SMTLIB2_KEYWORDS.contains(str));

    if (VALID_CHARS.matchesAllOf(str) && !DIGITS.matches(str.charAt(0))) {
      // simple symbol
      return str;
    } else {
      // quoted symbol
      return "|" + str + "|";
    }
  }
}
