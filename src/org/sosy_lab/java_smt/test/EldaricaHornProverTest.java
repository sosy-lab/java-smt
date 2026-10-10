/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IConstant;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.ITerm;
import ap.terfor.ConstantTerm;
import ap.terfor.preds.Predicate;
import ap.types.MonoSortedIFunction;
import ap.types.Sort;
import ap.types.Sort.Integer$;
import com.google.j2objc.annotations.Property.Suppress;
import java.util.Arrays;
import org.junit.Test;
import org.sosy_lab.java_smt.solvers.princess.eldarica.PrincessHornConverter;
import scala.collection.immutable.Seq;
import scala.collection.immutable.Seq$;
import scala.collection.immutable.Set;
import scala.jdk.javaapi.CollectionConverters;

public class EldaricaHornProverTest {

  @SuppressWarnings("unchecked")
  private IAtom atom(String name) {
    return new IAtom(new Predicate(name, 0), (Seq<ITerm>) Seq$.MODULE$.empty());
  }

  @SuppressWarnings("varargs")
  @SafeVarargs
  private <T> Set<T> set(T... values) {
    return CollectionConverters.asScala(Arrays.asList(values)).toSet();
  }

  @SuppressWarnings("varargs")
  @SafeVarargs
  private <T> Seq<T> seq(T... values) {
    return CollectionConverters.asScala(Arrays.asList(values)).toSeq();
  }


  @Test
  public void headWithoutBody() {
    var a = atom("a");

    IFormula input = a;


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head()).isEqualTo(a);
    assertThat(clause.body().toSet()).isEqualTo(set());
  }

  @Test
  public void multipleBodyAtomsAndHead() {
    var a = atom("a");
    var b = atom("b");
    var c = atom("c");
    var d = atom("d");

    IFormula input = new IBinFormula(IBinJunctor.Or(), new INot(new IBinFormula(IBinJunctor.And(),
        new IBinFormula(IBinJunctor.And(), b, c), d)), a);


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head()).isEqualTo(a);
    assertThat(clause.body().toSet()).isEqualTo(set(b, c, d));
  }

  @Test
  public void singleBodyWithHead() {
    var a = atom("a");
    var b = atom("b");


    IFormula input = new IBinFormula(IBinJunctor.Or(), new INot(b), a);


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head()).isEqualTo(a);
    assertThat(clause.body().toSet()).isEqualTo(set(b));
  }

  @Test
  public void predicateHead() {
    var args = seq((ITerm) new IConstant(new ConstantTerm("x")));
    var f = new IFunApp(new MonoSortedIFunction("f", seq(Integer$.MODULE$), Sort.Bool(), false,
        false), args);

    IFormula f0 = new IIntFormula(IIntRelation.EqZero(), f);


    var clause = new PrincessHornConverter().toClause(f0);

    assertThat(clause.head().toString()).isEqualTo(new IAtom(new Predicate("f", 1), args).toString());
    assertThat(clause.body().toSet()).isEqualTo(set());
  }

  @Test
  public void predicateHeadWithBody() {
    var args = seq((ITerm) new IConstant(new ConstantTerm("x")));
    var f = new IFunApp(new MonoSortedIFunction("f", seq(Integer$.MODULE$), Sort.Bool(), false,
        false), args);
    var h = new IFunApp(new MonoSortedIFunction("h", seq(Integer$.MODULE$), Sort.Bool(), false,
        false), args);

    IFormula f0 = new IIntFormula(IIntRelation.EqZero(), f);
    IFormula h0 = new IIntFormula(IIntRelation.EqZero(), h);

    IFormula input = new IBinFormula(IBinJunctor.Or(), new INot(h0), f0);


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head().toString()).isEqualTo(new IAtom(new Predicate("f", 1), args).toString());
    assertThat(clause.body().toSet().toString()).isEqualTo(set(new IAtom(new Predicate("h", 1),
        args).toString()).toString());
  }

  @Test
  public void constraintWithHeadAndBody() {
    var a = atom("a");
    var b = atom("b");
    var c = atom("c");


    IFormula constraint = new IIntFormula(IIntRelation.EqZero(),
        new IPlus(new IConstant(new ConstantTerm("d")),
            new IIntLit(IdealInt.apply(-1))));

    IFormula body = new IBinFormula(IBinJunctor.And(), b, c);

    IFormula input = new IBinFormula(IBinJunctor.Or(), new INot(new IBinFormula(IBinJunctor.And(),
        constraint, body)), a);


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head()).isEqualTo(a);
    assertThat(clause.body().toSet()).isEqualTo(set(b, c));
    assertThat(clause.constraint()).isEqualTo(constraint);
  }

  @Test
  public void constraintWithHead() {
    var a = atom("a");


    IFormula constraint = new IIntFormula(IIntRelation.EqZero(),
        new IPlus(new IConstant(new ConstantTerm("d")),
            new IIntLit(IdealInt.apply(-1))));

    IFormula input = new IBinFormula(IBinJunctor.Or(), new INot(constraint), a);


    var clause = new PrincessHornConverter().toClause(input);

    assertThat(clause.head()).isEqualTo(a);
    assertThat(clause.body().toSet()).isEqualTo(set());
    assertThat(clause.constraint()).isEqualTo(constraint);
  }

  // TODO: no head
}
