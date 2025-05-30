// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class SmtInterpolInterpolatingProver extends SmtInterpolAbstractProver<String>
    implements InterpolatingProverEnvironment<String> {

  SmtInterpolInterpolatingProver(
      SmtInterpolFormulaManager pMgr,
      Script pScript,
      Set<ProverOptions> options,
      ShutdownNotifier pShutdownNotifier) {
    super(pMgr, pScript, options, pShutdownNotifier);
  }

  @Override
  protected String addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    return super.addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<String> pTermNamesOfA)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(pTermNamesOfA),
        "interpolation can only be done over previously asserted formulas.");

    // SMTInterpol is not able to handle the trivial cases,
    // so we need to check them explicitly
    if (pTermNamesOfA.isEmpty()) {
      return mgr.getBooleanFormulaManager().makeBoolean(true);
    } else if (pTermNamesOfA.containsAll(annotatedTerms.peek().keySet())) {
      return mgr.getBooleanFormulaManager().makeBoolean(false);
    }

    Set<String> termNamesOfA = ImmutableSet.copyOf(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<String> termNamesOfB = Sets.difference(annotatedTerms.peek().keySet(), termNamesOfA);

    // build 2 groups:  (and A1 A2 A3...) , (and B1 B2 B3...)
    return Iterables.getOnlyElement(
        getSeqInterpolants(ImmutableList.of(termNamesOfA, termNamesOfB)));
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<String>> partitionedTermNames, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    final ImmutableSet<String> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitionedTermNames.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");
    assert InterpolatingProverEnvironment.checkTreeStructure(
        partitionedTermNames.size(), startOfSubTree);

    final Term[] formulas = new Term[partitionedTermNames.size()];
    for (int i = 0; i < formulas.length; i++) {
      formulas[i] = buildConjunctionOfNamedTerms(partitionedTermNames.get(i));
    }

    // get interpolants of groups
    final Term[] itps;
    try {
      itps = env.getInterpolants(formulas, startOfSubTree);
    } catch (UnsupportedOperationException e) {
      if (e.getMessage() != null && e.getMessage().startsWith("Cannot interpolate ")) {
        // Not a bug, interpolation procedure is incomplete
        throw new SolverException(e.getMessage(), e);
      } else {
        throw e;
      }
    } catch (SMTLIBException e) {
      if ("Timeout exceeded".equals(e.getMessage())) {
        shutdownNotifier.shutdownIfNecessary();
      }
      throw new AssertionError(e);
    }

    final List<BooleanFormula> result = new ArrayList<>();
    for (Term itp : itps) {
      result.add(mgr.encapsulateBooleanFormula(itp));
    }
    assert result.size() == startOfSubTree.length - 1;
    return result;
  }

  private Term buildConjunctionOfNamedTerms(Collection<String> termNames) {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(!termNames.isEmpty());

    if (termNames.size() == 1) {
      return env.term(Iterables.getOnlyElement(termNames));
    }
    return env.term("and", termNames.stream().map(env::term).toArray(Term[]::new));
  }
}
