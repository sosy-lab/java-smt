// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toITermSeq;

import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import ap.types.Sort;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.List;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

public class PrincessStringFormulaManager
    extends AbstractStringFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  PrincessStringFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  /**
   * Tries to parse an escaped unicode character
   *
   * <p>Returns the original String if parsing is not possible.
   */
  private static String literalOrSkip(String pToken) {
    String literal;
    if (pToken.startsWith("\\u{")) {
      if (pToken.length() > 9) {
        // Abort if there are too many digits
        // The longest allowed literal is \\u{d5 d4 d3 d2 d1}
        return pToken;
      }
      literal = pToken.substring(3, pToken.length() - 1);
    } else {
      if (pToken.length() != 6) {
        // Abort if there are not exactly 4 digits
        // The literal must have this form: \\u d3 d2 d1 d0
        return pToken;
      }
      literal = pToken.substring(2);
    }

    // Try to parse the digits as an (hexadecimal) integer
    // Abort if there is an error
    int value;
    try {
      value = Integer.parseInt(literal, 16);
    } catch (NumberFormatException e) {
      return pToken;
    }

    // Return the unicode letter if it fits into a single 16bit character
    // Abort otherwise
    char[] chars = Character.toChars(value);
    if (chars.length != 1) {
      return pToken;
    } else {
      return String.valueOf(chars[0]);
    }
  }

  /** Replace escape sequences for unicode letters with their UTF16 representation */
  private static String unescapeString(String pInput) {
    StringBuilder builder = new StringBuilder();
    while (!pInput.isEmpty()) {
      // Search for the next escape sequence
      int start = pInput.indexOf("\\u");
      if (start == -1) {
        // Append the rest of the String to the output if there are no more escaped unicode
        // characters
        builder.append(pInput);
        pInput = "";
      } else {
        // Store the prefix up to the escape sequence
        String prefix = pInput.substring(0, start);

        // Skip ahead and get the escape sequence
        pInput = pInput.substring(start);
        String value;
        if (pInput.charAt(2) == '{') {
          // Sequence has the form \\u{d5 d4 d3 d2 d1 d0}
          int stop = pInput.indexOf('}');
          Preconditions.checkArgument(stop != -1); // Panic if there is no closing bracket
          value = pInput.substring(0, stop + 1);
          pInput = pInput.substring(stop + 1);
        } else {
          // Sequence has the form \\u d3 d2 d1 d0
          int stop = 2;
          while (stop < pInput.length()) {
            char c = pInput.charAt(stop);
            if (Character.digit(c, 16) == -1) {
              break;
            }
            stop++;
          }
          value = pInput.substring(0, stop);
          pInput = pInput.substring(stop);
        }

        // Try to parse the escape sequence to replace it with its 16bit unicode character
        // If parsing fails just keep it in the String
        String nextToken = literalOrSkip(value);

        // Collect the prefix and the (possibly) translated escape sequence
        builder.append(prefix).append(nextToken);
      }
    }
    return builder.toString();
  }

  @Override
  protected IExpression makeStringImpl(String value) {
    return PrincessEnvironment.stringTheory.string2Term(unescapeString(value));
  }

  @Override
  protected IExpression makeVariableImpl(String pVar) {
    Sort t = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(t, pVar);
  }

  @Override
  protected IFormula equal(IExpression pParam1, IExpression pParam2) {
    return ((ITerm) pParam1).$eq$eq$eq((ITerm) pParam2);
  }

  @Override
  protected IFormula greaterThan(IExpression pParam1, IExpression pParam2) {
    // just reverse the order
    return lessThan(pParam2, pParam1);
  }

  @Override
  protected IFormula lessOrEquals(IExpression pParam1, IExpression pParam2) {
    // FIXME: Report this as a bug
    // This should also work, but fails if the two Strings are equal:
    // return new IAtom(PrincessEnvironment.stringTheory.str_$less$eq(), toITermSeq(pParam1,
    //    pParam2));
    return new IBinFormula(
        IBinJunctor.Or(),
        ((ITerm) pParam1).$eq$eq$eq((ITerm) pParam2),
        new IAtom(
            PrincessEnvironment.stringTheory.str_$less(),
            PrincessEnvironment.toITermSeq(List.of(pParam1, pParam2))));
  }

  @Override
  protected IFormula greaterOrEquals(IExpression pParam1, IExpression pParam2) {
    // just reverse the order
    return lessOrEquals(pParam2, pParam1);
  }

  @Override
  protected IFormula lessThan(IExpression pParam1, IExpression pParam2) {
    return new IAtom(PrincessEnvironment.stringTheory.str_$less(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm length(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_len(), toITermSeq(pParam));
  }

  @Override
  protected ITerm concatImpl(List<IExpression> parts) {
    ITerm result = (ITerm) makeStringImpl("");
    for (IExpression expr : parts) {
      result =
          new IFunApp(
              PrincessEnvironment.stringTheory.str_$plus$plus(),
              PrincessEnvironment.toSeq(ImmutableList.of(result, (ITerm) expr)));
    }
    return result;
  }

  @Override
  protected IFormula prefix(IExpression prefix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_prefixof(), toITermSeq(prefix, str));
  }

  @Override
  protected IFormula suffix(IExpression suffix, IExpression str) {
    return new IAtom(PrincessEnvironment.stringTheory.str_suffixof(), toITermSeq(suffix, str));
  }

  @Override
  protected IFormula in(IExpression str, IExpression regex) {
    return new IAtom(PrincessEnvironment.stringTheory.str_in_re(), toITermSeq(str, regex));
  }

  @Override
  protected IFormula contains(IExpression str, IExpression part) {
    return new IAtom(PrincessEnvironment.stringTheory.str_contains(), toITermSeq(str, part));
  }

  @Override
  protected ITerm indexOf(IExpression str, IExpression part, IExpression startIndex) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_indexof(), toITermSeq(str, part, startIndex));
  }

  @Override
  protected ITerm charAt(IExpression str, IExpression index) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_at(), toITermSeq(str, index));
  }

  @Override
  protected ITerm substring(IExpression str, IExpression index, IExpression length) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_substr(), toITermSeq(str, index, length));
  }

  @Override
  protected ITerm replace(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replace(), toITermSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm replaceAll(IExpression fullStr, IExpression target, IExpression replacement) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_replaceall(),
        toITermSeq(fullStr, target, replacement));
  }

  @Override
  protected ITerm makeRegexImpl(String value) {
    return new IFunApp(
        PrincessEnvironment.stringTheory.str_to_re(), toITermSeq(makeStringImpl(value)));
  }

  @Override
  protected ITerm noneImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_none(), toITermSeq());
  }

  @Override
  protected ITerm allImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_all(), toITermSeq());
  }

  @Override
  protected IExpression allCharImpl() {
    return new IFunApp(PrincessEnvironment.stringTheory.re_allchar(), toITermSeq());
  }

  @Override
  protected ITerm range(IExpression start, IExpression end) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_range(), toITermSeq());
  }

  @Override
  public RegexFormula cross(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_$plus(), toITermSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula optional(RegexFormula regex) {
    return wrapRegex(
        new IFunApp(PrincessEnvironment.stringTheory.re_opt(), toITermSeq(extractInfo(regex))));
  }

  @Override
  public RegexFormula difference(RegexFormula regex1, RegexFormula regex2) {
    return wrapRegex(
        new IFunApp(
            PrincessEnvironment.stringTheory.re_diff(),
            toITermSeq(extractInfo(regex1), extractInfo(regex2))));
  }

  @Override
  protected ITerm concatRegexImpl(List<IExpression> parts) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$plus$plus(), toITermSeq(parts));
  }

  @Override
  protected ITerm union(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_union(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm intersection(IExpression pParam1, IExpression pParam2) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_inter(), toITermSeq(pParam1, pParam2));
  }

  @Override
  protected ITerm closure(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_$times(), toITermSeq(pParam));
  }

  @Override
  protected ITerm complement(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.re_comp(), toITermSeq(pParam));
  }

  @Override
  protected ITerm toIntegerFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.str_to_int(), toITermSeq(pParam));
  }

  @Override
  protected ITerm toStringFormula(IExpression pParam) {
    return new IFunApp(PrincessEnvironment.stringTheory.int_to_str(), toITermSeq(pParam));
  }
}
