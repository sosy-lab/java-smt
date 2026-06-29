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
import ap.parser.IConstant;
import ap.parser.IEquation;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.ISortedQuantified;
import ap.parser.ISortedVariable;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.ITimes;
import ap.terfor.ConstantTerm;
import ap.terfor.conjunctions.Quantifier.ALL$;
import ap.terfor.preds.Predicate;
import ap.types.MonoSortedIFunction;
import ap.types.MonoSortedPredicate;
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

@SuppressWarnings({"unchecked", "PatternMatchingInstanceof"})
public class PrincessHornConverter {
  private final ArrayList<Predicate> predicates = new ArrayList<>();
  private int variables = 0;

  private Predicate toPredicate(final MonoSortedIFunction function) {
    // Predicate does not implement hashCode nor equals, this deduplicates the objects.
    for (Predicate predicate : this.predicates) {
      if (!predicate.name().equals(function.name()) || predicate.arity() != function.arity()) {
        continue;
      }
      return predicate;
    }
    Predicate predicate;
    if (function.argSorts().isEmpty()) {
      predicate = new Predicate(function.name(), function.arity());
    } else {
      predicate = new MonoSortedPredicate(function.name(), function.argSorts());
    }
    this.predicates.add(predicate);

    return predicate;
  }

  class ClauseContext {
    private final ArrayList<IConstant> parameters = new ArrayList<>();
    private IFormula constraint = new IBoolLit(true);


    private List<IFormula> flatten(final IBinFormula input) {
      if (input.j().equals(IBinJunctor.And())) {
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

      return List.of(toFormula(input));
    }


    private Clause toClause(final IAtom head, final IAtom rest) {
      var body = CollectionConverters.asScala(List.of(toFormula(rest))).toList();
      return new Clause(head, body, this.constraint);
    }

    private Clause toClause(final IAtom head, final IBoolLit rest) {
      this.constraint = this.constraint.andSimplify(rest);
      return toClause(head);
    }

    private Clause toClause(final IAtom head, final IEquation rest) {
      this.constraint = this.constraint.andSimplify(toFormula(rest));

      return toClause(head);
    }

    private Clause toClause(final IAtom head, final INot rest) {
      this.constraint = this.constraint.andSimplify(toFormula(rest));

      return toClause(head);
    }

    private Clause toClause(final IAtom head, final IIntFormula rest) {
      var atom = toAtom(rest);
      if (atom != null) {
        return new Clause(head, CollectionConverters.asScala(List.of(atom)).toList(),
            this.constraint);
      }
      this.constraint = this.constraint.andSimplify(toFormula(rest));
      return toClause(head);
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

    private Clause toClause(final IAtom head, final IFormula rest) {
      if (rest instanceof IAtom atom) {
        return toClause(head, atom);
      }
      if (rest instanceof IIntFormula _int) {
        return toClause(head, _int);
      }
      if (rest instanceof IBinFormula bin) {
        return toClause(head, bin);
      }
      if (rest instanceof IBoolLit lit) {
        return toClause(head, lit);
      }
      if (rest instanceof IEquation eq) {
        return toClause(head, eq);
      }
      if (rest instanceof INot not) {
        return toClause(head, not);
      }
      throw new RuntimeException("Unhandled clause: " + rest);
    }

    private IConstant createVariable() {
      return new IConstant(new ConstantTerm("T" + ++variables));
    }

    private IConstant addConstraint(final ITerm term) {
      if (term instanceof IConstant) {
        return (IConstant) term;
      }
      var variable = createVariable();
      var constraint = new IEquation(variable, toTerm(term));

      this.constraint = this.constraint.andSimplify(constraint);

      return variable;
    }

    private IAtom toFormula(final IAtom atom) {
      return new IAtom(atom.pred(), toTerm(atom.args()));
    }

    private IFormula toFormula(final IIntFormula i) {
      if (i.rel().equals(IIntRelation.EqZero()) && i.t() instanceof ITermITE ite) {
        if (ite.left() instanceof IIntLit lit && lit.value().isZero()) {
          return toFormula(ite.cond());
        }
        if (ite.right() instanceof IIntLit lit && lit.value().isZero()) {
          return toFormula(ite.cond().notSimplify());
        }
      }
      if (i.t() instanceof ITermITE) {
        throw new RuntimeException("ITE (TODO): " + i.t());
      }
      return new IIntFormula(i.rel(), toTerm(i.t()));
    }

    private IFormula toFormula(ITerm value, ITermITE ite) {
      value = toTerm(value);

      var condition = toFormula(ite.cond());

      var a = condition.andSimplify(new IEquation(value, toTerm(ite.left())));
      var b = condition.notSimplify().andSimplify(new IEquation(value, toTerm(ite.right())));

      return a.orSimplify(b);
    }

    private IFormula toFormula(final IEquation equation) {
      if (equation.left() instanceof ITermITE ite) {
        return toFormula(equation.right(), ite);
      }
      if (equation.right() instanceof ITermITE ite) {
        return toFormula(equation.left(), ite);
      }
      return new IEquation(toTerm(equation.left()), toTerm(equation.right()));
    }

    private IFormula toFormula(final IBinFormula bin) {
      var f1 = toFormula(bin.f1());
      var f2 = toFormula(bin.f2());
      if (bin.j().equals(IBinJunctor.Eqv())) {
        var a = f1.andSimplify(f2);
        var b = f1.notSimplify().andSimplify(f2.notSimplify());

        return a.orSimplify(b);
      }
      if (bin.j().equals(IBinJunctor.Or())) {
        return (f1.notSimplify().andSimplify(f2.notSimplify())).notSimplify();
      }
      return new IBinFormula(bin.j(), f1, f2);
    }

    private IFormula toFormula(final INot not) {
      return toFormula(not.subformula()).notSimplify();
    }

    private IFormula toFormula(final IFormulaITE ite) {
      var condition = toFormula(ite.cond());

      var a = condition.andSimplify(toFormula(ite.left()));
      var b = condition.notSimplify().andSimplify(toFormula(ite.right()));


      return a.orSimplify(b);
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
      if (formula instanceof IBoolLit lit) {
        return lit;
      }
      if (formula instanceof IFormulaITE ite) {
        return toFormula(ite);
      }

      throw new IllegalArgumentException("Unhandled formula: " + formula);
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

    private ITerm toTerm(final ITermITE ite) {
      var condition = toFormula(ite.cond());

      var variable = createVariable();
      var left = new IEquation(variable, toTerm(ite.left()));
      var right = new IEquation(variable, toTerm(ite.right()));


      var a = condition.andSimplify(left);
      var b = condition.notSimplify().andSimplify(right);


      this.constraint = this.constraint.andSimplify(a.orSimplify(b));

      return variable;
    }

    private ITerm toTerm(final ITerm term) {
      if (term instanceof IIntLit lit) {
        return lit;
      }
      if (term instanceof IConstant constant) {
        return constant;
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
      if (term instanceof IFunApp fun) {
        return new IFunApp(fun.fun(), toTerm(fun.args()));
      }
      if (term instanceof ITermITE ite) {
        return toTerm(ite);
      }

      throw new IllegalArgumentException("Unhandled term: " + term);
    }

    private ITerm toConstraint(final ITerm term) {
      if (term instanceof IConstant constant) {
        return constant;
      }
      if (term instanceof IIntLit lit) {
        return lit;
      }
      if (term instanceof ISortedVariable variable) {
        return toVariable(variable);
      }
      if (term instanceof IFunApp fun) {
        return new IFunApp(fun.fun(), toTerm(fun.args()));
      }
    //  if(term instanceof IPlus plus) {
    //    return new IPlus(toTerm(plus.t1()), toTerm(plus.t2()));
    //  }
    //  if(term instanceof ITimes times) {
    //    return new ITimes(times.coeff(), toTerm(times.subterm()));
    //  }
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
      if (formula.t() instanceof IFunApp t && formula.rel().equals(IIntRelation.EqZero())) {
        if (t.fun() instanceof MonoSortedIFunction fun) {
          return new IAtom(toPredicate(fun), toTerm(t.args()));
        }
      }

      return null;
    }

    private Clause toClause(final IAtom head) {
      assert head != null;
      return new Clause(head, List$.MODULE$.empty(), this.constraint);
    }

    private Clause toClause(final ISortedQuantified input) {
      if (input.quan() != ALL$.MODULE$) {
        throw new IllegalArgumentException("Invalid quantifier: " + input);
      }

      // Eldarica seems to always use for all quantifiers, so it is just removed
      return toClause(input.subformula());
    }

    private IFormula simplify(IFormula formula) {
      if (formula instanceof INot not) {
        return simplify(not);
      }
      return formula;
    }

    private IFormula simplify(INot not) {
      if (not.subformula() instanceof INot sub) {
        return simplify(sub.subformula());
      }
      return not;
    }

    private Clause toClause(final IBinFormula input) {
      if (!input.j().equals(IBinJunctor.Or())) {
        throw new IllegalArgumentException("Invalid formula junctor: " + input);
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
        throw new IllegalArgumentException("Unhandled clause: " + input);
      }

      IAtom head;

      if (other instanceof IAtom atom) {
        head = toFormula(atom);
      } else if (other instanceof IIntFormula) {
        head = toAtom((IIntFormula) other);
        if (head == null) {
          throw new RuntimeException("No head found: " + input);
        }
      } else {
        head = new IAtom(HornClauses.FALSE(), (Seq<ITerm>) Seq$.MODULE$.empty());
        this.constraint = this.constraint.andSimplify(simplify(toFormula(other).notSimplify()));

        return toClause(head, simplify(not.subformula()));
      }

      var subformula = simplify(not.subformula());
      if (subformula instanceof IAtom atom) {
        this.constraint = this.constraint.andSimplify(toFormula(atom).notSimplify());
        return toClause(head);
      }


      return toClause(head, subformula);
    }

    public Clause toClause(IFormula input) {
      if (input instanceof ISortedQuantified) {
        return toClause((ISortedQuantified) input);
      }
      if (input instanceof IAtom) {
        return toClause((IAtom) input);
      }
      if (input instanceof IBinFormula) {
        return toClause((IBinFormula) input);
      }
      if (input instanceof IIntFormula) {
        return toClause(toAtom((IIntFormula) input));
      }

      throw new IllegalArgumentException("Unhandled clause: " + input);
    }
  }

  public Clause toClause(IFormula input) {
    var context = new ClauseContext();

    return context.toClause(input);
  }
}
