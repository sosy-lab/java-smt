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

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IEquation;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.ISortedQuantified;
import ap.parser.ISortedVariable;
import ap.parser.ITerm;
import ap.parser.ITimes;
import ap.terfor.ConstantTerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.preds.Predicate;
import ap.types.MonoSortedIFunction;
import ap.types.Sort.Integer$;
import ap.types.SortedConstantTerm;
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
  private final ArrayList<IConstant> parameters = new ArrayList<>();
  private int variables = 0;

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

  class ClauseContext {
    private IFormula constraint = new IBoolLit(true);


    private List<IFormula> flatten(final IBinFormula input) {
      if (input.j() == IBinJunctor.And()) {
        return flattenAnd(input);
      }

      return List.of(toFormula(input));
    }

    private List<IFormula> flattenAnd(final IBinFormula input) {
      final ArrayList<IFormula> atoms = new ArrayList<>();
      atoms.addAll(flatten(input.f1()));
      atoms.addAll(flatten(input.f2()));

      return atoms;
    }

    private List<IFormula> flatten(final IFormula input) {
      if (input instanceof IBinFormula) {
        return flatten((IBinFormula) input);
      }

      return List.of(input);
    }

    private Clause toClause(final IAtom head, final IAtom rest) {
      return new Clause(head, CollectionConverters.asScala(List.of(rest)).toList(),
          this.constraint);
    }

    private Clause toClause(final IAtom head, final IIntFormula rest) {
      var atom = toAtom(rest);
      if (atom != null) {
        return new Clause(head, CollectionConverters.asScala(List.of(atom)).toList(),
            this.constraint);
      }
      return new Clause(head, List$.MODULE$.empty(), this.constraint.andSimplify(toFormula(rest)));
    }

    private Clause toClause(final IAtom head, final IBinFormula rest) {
      List<IAtom> body = new ArrayList<>();

      for (IFormula and : flatten(rest)) {
        if (and instanceof IAtom atom && atom.args().isEmpty()) {
          body.add(new IAtom(atom.pred(), toTerm(atom.args())));
          continue;
        }
        if (and instanceof IIntFormula) {
          var atom = toAtom((IIntFormula) and);
          if (atom != null) {
            body.add(atom);
            continue;
          }
        }

        constraint = constraint.andSimplify(toFormula(and));
      }


      return new Clause(head, CollectionConverters.asScala(body).toList(), constraint);
    }

    private Clause toClause(final IAtom head, final IFormula rest, final IFormula constraint) {
      // INPUT: ((B1 = 0) & C2) ; constraint: C1
      // CLAUSE: Clause(FALSE, List(B1), (C2 & !C1))
      var clause = toClause(head, rest);

      return new Clause(clause.head(), clause.body(), new IBinFormula(IBinJunctor.And(),
          clause.constraint(), this.constraint.andSimplify(new INot(constraint))));
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

    private IConstant addConstraint(final ITerm term) {
      if (term instanceof IConstant) {
        return (IConstant) term;
      }
      var variable = new IConstant(new ConstantTerm("T" + ++variables));
      var constraint = new IEquation(variable, term);

      this.constraint = this.constraint.andSimplify(constraint);

      return variable;
    }

    private IAtom toFormula(final IAtom atom) {
      return new IAtom(atom.pred(), toTerm(atom.args()));
    }

    private IIntFormula toFormula(final IIntFormula i) {
      return new IIntFormula(i.rel(), toTerm(i.t()));
    }

    private IEquation toFormula(final IEquation equation) {
      return new IEquation(toTerm(equation.left()), toTerm(equation.right()));
    }

    private IBinFormula toFormula(final IBinFormula bin) {
      return new IBinFormula(bin.j(), toFormula(bin.f1()),
          toFormula(bin.f2()));
    }

    private INot toFormula(final INot not) {
      return new INot(toFormula(not.subformula()));
    }

    private IFormula toFormula(final IFormula formula) {
      if (formula instanceof IAtom atom) {
        return toFormula(atom);
      }
      if (formula instanceof IIntFormula i) {
        return toFormula(i);
      }
      if (formula instanceof IEquation equation) {
        return toFormula(equation);
      }
      if (formula instanceof IBinFormula bin) {
        return toFormula(bin);
      }
      if (formula instanceof INot bin) {
        return toFormula(bin);
      }

      return formula;
    }

    private IConstant toVariable(final ISortedVariable variable) {
      var name = "V" + variable.index();

      for (IConstant constant : parameters) {
        if (constant.c().name().equals(name)) {
          return constant;
        }
      }

      ConstantTerm term;

      if (variable.sort() == Integer$.MODULE$) {
        term = new ConstantTerm(name);
      } else {
        term = new SortedConstantTerm(name, variable.sort());
      }

      var constant = new IConstant(term);
      parameters.add(constant);
      return constant;
    }

    private ITerm toTerm(final IdealInt term) {
      return new IIntLit(term);
    }

    private ITerm toTerm(final ITerm term) {
      if (term instanceof IIntLit lit) {
        return lit;
      }
      if (term instanceof ISortedVariable variable) {
        return toVariable(variable);
      }
      if (term instanceof IPlus plus) {
        return new IPlus(toTerm(plus.t1()), toTerm(plus.t2()));
      }
      if (term instanceof ITimes times) {
        return new ITimes(times.coeff(), toTerm(times.subterm()));
      }
      // TODO: epsilon, ITermITE, function

      return term;
    }

    private ITerm toConstraint(final ITerm term) {
      if (term instanceof IIntLit lit) {
        return lit;
      }
      if (term instanceof ISortedVariable variable) {
        return toVariable(variable);
      }
      if (term instanceof IFunApp fun) {
        return addConstraint(new IFunApp(fun.fun(), toTerm(fun.args())));
      }
      return addConstraint(toTerm(term));
    }

    private Seq<ITerm> toTerm(final Seq<ITerm> terms) {
      final var output = new ArrayList<ITerm>();

      for (ITerm term : CollectionConverters.asJava(terms)) {
        output.add(toConstraint(term));
      }

      return CollectionConverters.asScala(output).toSeq();
    }

    @Nullable
    private IAtom toAtom(final IIntFormula formula) {
      if (formula.t() instanceof IFunApp t && formula.rel() == IIntRelation.EqZero()) {
        if (t.fun() instanceof MonoSortedIFunction fun) {
          return new IAtom(toPredicate(fun), toTerm(t.args()));
        }
      }

      return null;
    }

    private Clause toClause(final IAtom input) {
      return new Clause(input, List$.MODULE$.empty(), this.constraint);
    }

    private Clause toClause(final ISortedQuantified input) {
      if (input.quan() != ALL$.MODULE$) {
        throw new IllegalArgumentException("Illegal horn clause: " + input);
      }

      return toClause(input.subformula()); // TODO: Really?
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

      if (other instanceof IAtom atom) {
        head = toFormula(atom);
      } else if (other instanceof IIntFormula) {
        head = toAtom((IIntFormula) other);
        if (head == null) {
          throw new RuntimeException("TODO");
        }
      } else {
        head = new IAtom(HornClauses.FALSE(), (Seq<ITerm>) Seq$.MODULE$.empty());

        // TODO: (expected) Clause(FALSE,List(mc(P1, P0)),!(!((101 + -1 * P1) >= 0) | (P0 = 92)))
        // TODO: (actual  ) Clause(FALSE,List(mc(P1, P0)),(((101 + -1 * P1) >= 0) & !(P0 = 91)))
        return toClause(head, not.subformula(), toFormula(other));
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

  public Clause toClause(IFormula input) {
    var context = new ClauseContext();

    return context.toClause(input);
  }
}
