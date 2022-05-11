// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.base.Preconditions;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

class SmtInterpolTheoremProver extends SmtInterpolAbstractProver<Void, Term>
    implements ProverEnvironment {

  SmtInterpolTheoremProver(
      SmtInterpolFormulaManager pMgr,
      Script pEnv,
      Set<ProverOptions> options,
      ShutdownNotifier pShutdownNotifier) {
    super(pMgr, pEnv, options, pShutdownNotifier);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    Term t = mgr.extractInfo(constraint);
    if (generateUnsatCores) {
      String termName = generateTermName();
      Term annotated = env.annotate(t, new Annotation(":named", termName));
      annotatedTerms.put(termName, t);
      env.assertTerm(annotated);
    } else {
      env.assertTerm(t);
    }
    assertedFormulas.peek().add(t);
    return null;
  }

  @Override
  protected Collection<Term> getAssertedTerms() {
    List<Term> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }
}
