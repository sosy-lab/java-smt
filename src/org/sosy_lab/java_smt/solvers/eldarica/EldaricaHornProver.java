// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.eldarica;

import ap.api.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.terfor.preds.Predicate;
import ap.types.MonoSortedIFunction;
import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import lazabs.horn.HornAPI;
import lazabs.horn.bottomup.HornClauses.Clause;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.princess.PrincessAbstractProver;
import org.sosy_lab.java_smt.solvers.princess.PrincessFormulaCreator;
import org.sosy_lab.java_smt.solvers.princess.PrincessFormulaManager;
import scala.collection.immutable.List$;
import scala.jdk.javaapi.CollectionConverters;

public class EldaricaHornProver extends PrincessAbstractProver<Void> implements ProverEnvironment {
  private final HornAPI horn;
  private final ArrayList<Clause> clauses = new ArrayList<>();

  public EldaricaHornProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
    this.horn = new HornAPI(new HornAPI.CEGAROptions()); // TODO: options
  }

  private static List<IFormula> flatten(final IBinFormula input) {
    if (input.j() != IBinJunctor.And()) {
      throw new IllegalArgumentException("Illegal horn clause: " + input);
    }

    final ArrayList<IFormula> atoms = new ArrayList<>();
    atoms.addAll(flatten(input.f1()));
    atoms.addAll(flatten(input.f2()));

    return atoms;
  }

  private static List<IFormula> flatten(final IFormula input) {
    if (input instanceof IBinFormula) {
      return flatten((IBinFormula) input);
    }

    return List.of(input);
  }

  private static Clause toClause(final IAtom head, final IFormula rest) {
    if (rest instanceof IAtom) {
      return new Clause(head, CollectionConverters.asScala(List.of((IAtom) rest)).toList(),
          new IBoolLit(true));
    }
    if (rest instanceof IIntFormula) {
      var atom = toAtom((IIntFormula) rest);
      if (atom != null) {
        return new Clause(head, CollectionConverters.asScala(List.of(atom)).toList(),
            new IBoolLit(true));
      }
      return new Clause(head, List$.MODULE$.empty(), rest);
    }

    if (rest instanceof IBinFormula) {
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

        if (constraint != null) {
          throw new IllegalArgumentException("Duplicated constraints: " + rest);
        }
        constraint = and;
      }


      var _constraint = constraint == null ? new IBoolLit(true) : constraint;

      return new Clause(head, CollectionConverters.asScala(body).toList(), _constraint);
    }

    throw new RuntimeException("TODO");
  }


  @Nullable
  private static IAtom toAtom(final IIntFormula formula) {
    if (formula.t() instanceof IFunApp && formula.rel() == IIntRelation.EqZero()) {
      var t = (IFunApp) formula.t();
      if (t.fun() instanceof MonoSortedIFunction) {
        var fun = (MonoSortedIFunction) t.fun();
        return new IAtom(new Predicate(fun.name(), fun.arity()), t.args());
      }
    }

    return null;
  }

  private static Clause toClause(final IAtom input) {
    return new Clause(input, List$.MODULE$.empty(), new IBoolLit(true));
  }

  private static Clause toClause(final IBinFormula input) {
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
      throw new RuntimeException("TODO");
    }


    return toClause(head, not.subformula());
  }

  public static Clause toClause(IFormula input) {
    if (input instanceof IAtom) {
      return toClause((IAtom) input);
    }
    if (input instanceof IBinFormula) {
      return toClause((IBinFormula) input);
    }
    if (input instanceof IIntFormula) {
      return toClause(toAtom((IIntFormula) input));
    }

    throw new IllegalArgumentException("Illegal horn clause: " + input);
  }

  private void addConstraint1(BooleanFormula constraint) {
    Preconditions.checkState(!closed);

    final int formulaId = idGenerator.getFreshId();
    partitions.push(partitions.pop().putAndCopy(formulaId, constraint));
    api.setPartitionNumber(formulaId);

    final IFormula formula = (IFormula) mgr.extractInfo(constraint);
    // TODO: purpose?
    var assertion =
        api.abbrevSharedExpressions(formula, creator.getEnv().getMinAtomsForAbbreviation());

    if (assertion.isTrue()) {
      return; // TODO: handle false
    }

    var clause = toClause(assertion);

    this.clauses.add(clause);
  }

  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    addConstraint1(constraint);
    return null;
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException {
    return !this.horn.isSat(CollectionConverters.asScala(this.clauses));
  }
}
