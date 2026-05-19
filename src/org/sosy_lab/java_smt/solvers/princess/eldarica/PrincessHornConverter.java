/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess.eldarica;

import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.ISortedQuantified;
import ap.parser.ITerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.preds.Predicate;
import ap.types.MonoSortedIFunction;
import java.util.ArrayList;
import java.util.List;
import lazabs.horn.bottomup.HornClauses;
import lazabs.horn.bottomup.HornClauses.Clause;
import org.checkerframework.checker.nullness.qual.Nullable;
import scala.collection.Seq$;
import scala.collection.immutable.List$;
import scala.collection.immutable.Seq;
import scala.jdk.javaapi.CollectionConverters;

public class PrincessHornConverter {
  private final ArrayList<Predicate> predicates = new ArrayList<>();

  private Predicate toPredicate(final MonoSortedIFunction function) {
    // Predicate does not implement hashCode nor equals, this deduplicates the objects. Not 100%
    // sure if that is needed
    for (Predicate predicate : this.predicates) {
      if (!predicate.name().equals(function.name()) || predicate.arity() != function.arity()) {
        continue;
      }
      return predicate;
    }
    Predicate predicate = new Predicate(function.name(), function.arity());
    this.predicates.add(predicate);

    return predicate;
  }

  private List<IFormula> flatten(final IBinFormula input) {
    if (input.j() == IBinJunctor.And()) {
      return flattenAnd(input);
    }
    if (input.j() == IBinJunctor.Or()) {
      return flattenOr(input);
    }

    throw new IllegalArgumentException("Illegal horn clause: " + input);
  }

  private List<IFormula> flattenAnd(final IBinFormula input) {
    final ArrayList<IFormula> atoms = new ArrayList<>();
    atoms.addAll(flatten(input.f1()));
    atoms.addAll(flatten(input.f2()));

    return atoms;
  }

  private List<IFormula> flattenOr(final IBinFormula input) {
    final ArrayList<IFormula> atoms = new ArrayList<>();

    throw new IllegalArgumentException("Illegal horn clause: " + input);
  }

  private List<IFormula> flatten(final IFormula input) {
    if (input instanceof IBinFormula) {
      return flatten((IBinFormula) input);
    }

    return List.of(input);
  }

  private Clause toClause(final IAtom head, final IAtom rest) {
    return new Clause(head, CollectionConverters.asScala(List.of(rest)).toList(),
        new IBoolLit(true));
  }

  private Clause toClause(final IAtom head, final IIntFormula rest) {
    var atom = toAtom(rest);
    if (atom != null) {
      return new Clause(head, CollectionConverters.asScala(List.of(atom)).toList(),
          new IBoolLit(true));
    }
    return new Clause(head, List$.MODULE$.empty(), rest);
  }

  private Clause toClause(final IAtom head, final IBinFormula rest) {
    List<IAtom> body = new ArrayList<>();
    IFormula constraint = null;

    for (IFormula and : flatten(rest)) {
      if (and instanceof IAtom) {
        body.add((IAtom) and);
        continue;
      }
      if (and instanceof IIntFormula) {
        var atom = toAtom((IIntFormula) and);
        if (atom != null) {
          body.add(atom);
          continue;
        }
      }

      if (constraint == null) {
        constraint = and;
      } else {
        constraint = new IBinFormula(IBinJunctor.And(), constraint, and);
      }
    }


    var _constraint = constraint == null ? new IBoolLit(true) : constraint;

    return new Clause(head, CollectionConverters.asScala(body).toList(), _constraint);
  }

  private Clause toClause(final IAtom head, final IFormula rest, final IFormula constraint) {
    // INPUT: ((B1 = 0) & C2) ; constraint: C1
    // CLAUSE: Clause(FALSE, List(B1), (C2 & !C1))
    var clause = toClause(head, rest);

    return new Clause(clause.head(), clause.body(), new IBinFormula(IBinJunctor.And(),
        clause.constraint(), new INot(constraint)));
  }

  private Clause toClause(final IAtom head, final IFormula rest) {
    if (rest instanceof IAtom) {
      return toClause(head, (IAtom) rest);
    }
    if (rest instanceof IIntFormula) {
      return toClause(head, (IIntFormula) rest);
    }

    if (rest instanceof IBinFormula) {
      return toClause(head, (IBinFormula) rest);
    }

    throw new RuntimeException("TODO");
  }

  @Nullable
  private IAtom toAtom(final IIntFormula formula) {
    if (formula.t() instanceof IFunApp t && formula.rel() == IIntRelation.EqZero()) {
      if (t.fun() instanceof MonoSortedIFunction fun) {
        return new IAtom(toPredicate(fun), t.args());
      }
    }

    return null;
  }

  private Clause toClause(final IAtom input) {
    return new Clause(input, List$.MODULE$.empty(), new IBoolLit(true));
  }

  private Clause toClause(final ISortedQuantified input) {
    if (input.quan() != ALL$.MODULE$) {
      throw new IllegalArgumentException("Illegal horn clause: " + input);
    }

    return toClause(input.subformula());
  }

  private Clause toClause(final IBinFormula input) {
    if (input.j() != IBinJunctor.Or()) {
      throw new IllegalArgumentException("Illegal horn clause: " + input);
    }

    INot not;
    IFormula other;


    if (input.f1() instanceof INot) {
      not = (INot) input.f1();
      other = input.f2();
    } else if (input.f2() instanceof INot) {
      not = (INot) input.f2();
      other = input.f1();
    } else {
      throw new RuntimeException("TODO");
    }

    IAtom head;

    if (other instanceof IAtom) {
      head = (IAtom) other;
    } else if (other instanceof IIntFormula) {
      head = toAtom((IIntFormula) other);
      if (head == null) {
        throw new RuntimeException("TODO");
      }
    } else {
      head = new IAtom(HornClauses.FALSE(), (Seq<ITerm>) Seq$.MODULE$.empty());

      // TODO: (expected) Clause(FALSE,List(mc(P1, P0)),!(!((101 + -1 * P1) >= 0) | (P0 = 92)))
      // TODO: (actual  ) Clause(FALSE,List(mc(P1, P0)),(((101 + -1 * P1) >= 0) & !(P0 = 91)))
      return toClause(head, not.subformula(), other);
    }


    return toClause(head, not.subformula());
  }

  public Clause toClause(IFormula input) {
    if (input instanceof ISortedQuantified) {
      return toClause((ISortedQuantified) input);
    }
    if (input instanceof IAtom) {
      return toClause((IAtom) input);
    }
    if (input instanceof IBinFormula) {
      // (!(((((((((_0 = _8) & (_1 = _9)) & (_2 = _10)) & (_3 = _11)) & (_4 = _12)) & (_5 = _13)) & (_6 = _14)) & (_7 = _15)) & true) | (h1(_15, _14, _13, _12, _11, _10, _9, _8, _7, _6, _5, _4, _3, _2, _1, _0) = 0))
      // Clause(h1(P15, P14, P13, P12, P11, P10, P9, P8, P7, P6, P5, P4, P3, P2, P1, P0),List(),((((((((P0 = P8) & (P1 = P9)) & (P2 = P10)) & (P3 = P11)) & (P4 = P12)) & (P5 = P13)) & (P6 = P14)) & (P7 = P15)))
      return toClause((IBinFormula) input);
    }
    if (input instanceof IIntFormula) {
      return toClause(toAtom((IIntFormula) input));
    }

    throw new IllegalArgumentException("Illegal horn clause: " + input);
  }
}
