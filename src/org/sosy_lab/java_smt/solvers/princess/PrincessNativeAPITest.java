/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static scala.collection.JavaConverters.collectionAsScalaIterableConverter;

import ap.api.PartialModel;
import ap.api.SimpleAPI;
import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IIntLit;
import ap.parser.INot;
import ap.parser.ITerm;
import ap.theories.rationals.Rationals$;
import ap.theories.strings.StringTheory;
import ap.types.Sort;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import java.util.Comparator;
import java.util.List;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import ostrich.OFlags;
import ostrich.OstrichStringTheory;
import ostrich.automata.Transducer;
import scala.Enumeration.Value;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;

public class PrincessNativeAPITest {
  private StringTheory stringTheory;
  private SimpleAPI api;

  @Before
  public void init() {
    api =
        SimpleAPI.apply(
            SimpleAPI.apply$default$1(),
            SimpleAPI.apply$default$2(),
            SimpleAPI.apply$default$3(),
            SimpleAPI.apply$default$4(),
            SimpleAPI.apply$default$5(),
            SimpleAPI.apply$default$6(),
            SimpleAPI.apply$default$7(),
            SimpleAPI.apply$default$8(),
            SimpleAPI.apply$default$9(),
            SimpleAPI.apply$default$10(),
            SimpleAPI.apply$default$11());
    ImmutableList<Tuple2<String, Transducer>> empty = ImmutableList.of();
    stringTheory =
        new OstrichStringTheory(
            JavaConverters.asScalaIteratorConverter(empty.iterator()).asScala().toSeq(),
            new OFlags(
                OFlags.$lessinit$greater$default$1(),
                OFlags.$lessinit$greater$default$2(),
                OFlags.$lessinit$greater$default$3(),
                OFlags.$lessinit$greater$default$4(),
                OFlags.$lessinit$greater$default$5(),
                OFlags.$lessinit$greater$default$6(),
                OFlags.$lessinit$greater$default$7(),
                OFlags.$lessinit$greater$default$8(),
                OFlags.$lessinit$greater$default$9(),
                OFlags.$lessinit$greater$default$10(),
                OFlags.$lessinit$greater$default$11(),
                OFlags.$lessinit$greater$default$12(),
                OFlags.$lessinit$greater$default$13(),
                OFlags.$lessinit$greater$default$14(),
                OFlags.$lessinit$greater$default$15()));
  }

  private static final ImmutableList<String> WORDS =
      FluentIterable.from(
              ImmutableList.of(
                  "", "a", "b", "A", "B", "aa", "ab", "aA", "aB", "ba", "bb", "bA", "bB", "Aa",
                  "Ab", "AA", "AB", "Ba", "Bb", "BA", "BB"))
          .toSortedList(Comparator.comparing(s -> s));

  @Test
  public void equalTest() {
    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 0; j < WORDS.size(); j++) {
        ITerm a = stringTheory.string2Term(WORDS.get(i));
        ITerm b = stringTheory.string2Term(WORDS.get(j));

        IFormula formula = (i == j) ? a.$eq$eq$eq(b) : a.$eq$div$eq(b);
        api.push();
        api.addAssertion(formula);
        Value r = api.checkSat(true);
        api.pop();

        assertThat(r.toString()).isEqualTo("Sat");
      }
    }
  }

  @Test
  public void lessThanTest() {
    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 0; j < WORDS.size(); j++) {
        ITerm a = stringTheory.string2Term(WORDS.get(i));
        ITerm b = stringTheory.string2Term(WORDS.get(j));

        api.push();
        IFormula formula =
            new IAtom(
                stringTheory.str_$less(),
                collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
        if (i >= j) {
          formula = new INot(formula);
        }
        api.addAssertion(formula);
        Value r = api.checkSat(true);
        api.pop();

        assertWithMessage("Princess says %s < %s does not hold", a, b)
            .that(r.toString())
            .isEqualTo("Sat");
      }
    }
  }

  @Ignore
  @Test
  public void lessOrEqualTest() {
    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 0; j < WORDS.size(); j++) {
        ITerm a = stringTheory.string2Term(WORDS.get(i));
        ITerm b = stringTheory.string2Term(WORDS.get(j));

        api.push();
        IFormula formula =
            new IAtom(
                stringTheory.str_$less$eq(),
                collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
        if (i > j) {
          formula = new INot(formula);
        }
        api.addAssertion(formula);
        Value r = api.checkSat(true);
        api.pop();

        assertWithMessage("Princess says %s <= %s does not hold", a, b)
            .that(r.toString())
            .isEqualTo("Sat");
      }
    }
  }

  @Ignore
  @Test
  public void lessOrEqualBrokenTest() {
    ITerm a = stringTheory.string2Term("a");
    ITerm b = stringTheory.string2Term("a");
    IFormula formula =
        new IAtom(
            stringTheory.str_$less$eq(),
            collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
    api.addAssertion(formula);
    Value r = api.checkSat(true);
    assertThat(r.toString()).isEqualTo("Sat");
  }

  @Test
  public void lessOrEqualFixedTest() {
    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 0; j < WORDS.size(); j++) {
        ITerm a = stringTheory.string2Term(WORDS.get(i));
        ITerm b = stringTheory.string2Term(WORDS.get(j));

        api.push();
        IFormula formula =
            new IBinFormula(
                IBinJunctor.Or(),
                a.$eq$eq$eq(b),
                new IAtom(
                    stringTheory.str_$less(),
                    collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq()));
        if (i > j) {
          formula = new INot(formula);
        }
        api.addAssertion(formula);
        Value r = api.checkSat(true);
        api.pop();

        assertWithMessage("Princess says %s <= %s does not hold", a, b)
            .that(r.toString())
            .isEqualTo("Sat");
      }
    }
  }

  @Test
  public void constContainsTest() {
    ITerm a = stringTheory.string2Term("ab");
    ITerm b = stringTheory.string2Term("b");
    IFormula formula =
        new IAtom(
            stringTheory.str_contains(),
            collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
    api.addAssertion(formula);
    Value r = api.checkSat(true);
    assertThat(r.toString()).isEqualTo("Sat");
  }

  @Ignore
  @Test
  public void variableContainsTest() {
    ITerm a = api.createConstant("var1", stringTheory.StringSort());
    ITerm b = api.createConstant("var2", stringTheory.StringSort());
    IFormula formula =
        new IAtom(
            stringTheory.str_contains(),
            collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
    api.addAssertion(formula);
    Value r = api.checkSat(true);
    assertThat(r.toString()).isEqualTo("Sat");
  }

  @Ignore
  @Test
  public void variableLessOrEqualTest() {
    ITerm a = api.createConstant("var1", stringTheory.StringSort());
    ITerm b = api.createConstant("var2", stringTheory.StringSort());
    IFormula formula =
        new IAtom(
            stringTheory.str_$less$eq(),
            collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq());
    api.addAssertion(formula);
    Value r = api.checkSat(true);
    assertThat(r.toString()).isEqualTo("Sat");
  }

  @Ignore
  @Test
  public void prefixSuffixTest() {
    // Running backward propagation
    // Warning: cyclic definitions found, ignoring some function applications
    //   ... disequality is not satisfied: suffix != prefix
    //
    // ap.api.SimpleAPI$SimpleAPIForwardedException: Internal exception: java.lang.Exception:
    // Model extraction failed: Right(List(0)) != Right(Vector(1))

    ITerm a = api.createConstant("var1", stringTheory.StringSort());
    ITerm b = api.createConstant("var2", stringTheory.StringSort());
    IFormula formula =
        new IBinFormula(
            IBinJunctor.Or(),
            new INot(
                new IBinFormula(
                    IBinJunctor.And(),
                    new IAtom(
                        stringTheory.str_prefixof(),
                        collectionAsScalaIterableConverter(List.of(a, b)).asScala().toSeq()),
                    new IAtom(
                        stringTheory.str_suffixof(),
                        collectionAsScalaIterableConverter(List.of(b, a)).asScala().toSeq()))),
            a.$eq$eq$eq(b));
    api.addAssertion(new INot(formula));
    Value r = api.checkSat(true);
    assertThat(r.toString()).isEqualTo("Unsat");
  }

  @Test
  public void testIntegerEvaluation() {
    // See bug report:
    // https://github.com/uuverifiers/princess/issues/7
    ITerm num2 = new IIntLit(IdealInt.apply(2));
    ITerm x = api.createConstant("x", Sort.Integer$.MODULE$);
    IFormula eq = num2.$eq$eq$eq(x);
    api.addAssertion(eq);
    Value result = api.checkSat(true); // --> SAT
    assertThat(result.toString()).isEqualTo("Sat");
    PartialModel model = api.partialModel();
    Option<IExpression> eval = model.evalExpression(num2.$plus(x));
    System.out.println(eval); // -> Some(4) :-) GOOD BEHAVIOUR
    assertThat(eval.nonEmpty()).isTrue();
  }

  @Ignore
  @Test
  public void testRationalEvaluation() {
    // See bug report:
    // https://github.com/uuverifiers/princess/issues/7
    ITerm num2 = Rationals$.MODULE$.int2ring(new IIntLit(IdealInt.apply(2)));
    ITerm x = api.createConstant("x", Rationals$.MODULE$.dom());
    IFormula eq = num2.$eq$eq$eq(x);
    api.addAssertion(eq);
    Value result = api.checkSat(true); // --> SAT
    assertThat(result.toString()).isEqualTo("Sat");
    PartialModel model = api.partialModel();
    Option<IExpression> eval = model.evalExpression(num2.$plus(x));
    System.out.println(eval); // -> None :-( BAD BEHAVIOUR
    assertThat(eval.nonEmpty()).isTrue();
  }

  @Test
  public void testRationalEvaluationFixed() {
    // See bug report:
    // https://github.com/uuverifiers/princess/issues/7
    ITerm num2 = Rationals$.MODULE$.int2ring(new IIntLit(IdealInt.apply(2)));
    ITerm x = api.createConstant("x", Rationals$.MODULE$.dom());
    IFormula eq = num2.$eq$eq$eq(x);
    api.addAssertion(eq);
    Value result = api.checkSat(true); // --> SAT
    assertThat(result.toString()).isEqualTo("Sat");
    IExpression eval = api.evalToTerm(num2.$plus(x));
    System.out.println(eval); // -> None :-( BAD BEHAVIOUR
    assertThat(eval.toString()).isEqualTo("4");
  }

  @Ignore
  @Test
  public void testRationalEvaluation2() {
    // See bug report:
    // https://github.com/uuverifiers/princess/issues/8
    ITerm num2 = Rationals$.MODULE$.int2ring(new IIntLit(IdealInt.apply(2)));
    ITerm x = api.createConstant("x", Rationals$.MODULE$.dom());
    Value result = api.checkSat(true); // --> we have not added any constraints, so this is SAT
    assertThat(result.toString()).isEqualTo("Sat");
    PartialModel model = api.partialModel();
    Option<IExpression> eval = model.evalExpression(Rationals$.MODULE$.div(x, num2)); // --> CRASH
    System.out.println(eval); // -> Some(0) would be nice to receive
    assertThat(eval.nonEmpty()).isTrue();
  }

  @Test
  public void testRationalEvaluation2Workaround() {
    // See bug report:
    // https://github.com/uuverifiers/princess/issues/8
    api.addTheory(Rationals$.MODULE$);
    ITerm num2 = Rationals$.MODULE$.int2ring(new IIntLit(IdealInt.apply(2)));
    ITerm x = api.createConstant("x", Rationals$.MODULE$.dom());
    Value result = api.checkSat(true); // --> we have not added any constraints, so this is SAT
    assertThat(result.toString()).isEqualTo("Sat");
    IExpression eval = api.evalToTerm(Rationals$.MODULE$.div(x, num2)); // --> CRASH
    System.out.println(eval); // -> Some(0) would be nice to receive
    assertThat(eval.toString()).isEqualTo("Rat_frac(0, 1)");
  }
}
