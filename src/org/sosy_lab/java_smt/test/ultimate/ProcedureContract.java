/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package org.sosy_lab.java_smt.test.ultimate;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import java.util.Collections;
import java.util.Objects;
import java.util.Set;

/**
 * A contract specifying the behaviour of a procedure (in Boogie or the ICFG) or function (in C).
 *
 * <p>The behaviour is specified using up to three kinds of clauses:
 *
 * <ol>
 *   <li>A "requires" clause specifies a precondition that must hold before a call.
 *   <li>An "ensures" clause specifies a relation guaranteed to hold between the state before the
 *       call and the state at the procedure exit.
 *   <li>Optionally, a "modifies" clause specifies a subset of global variables that the procedure
 *       may write to. Writes to any other global state is forbidden.
 * </ol>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @param <E> The type of expressions
 * @param <V> The type of variables
 */
public class ProcedureContract<E, V> {
  @Visualizable private final String mProcedure;

  @Visualizable private final E mRequires;

  @Visualizable private final E mEnsures;

  @Visualizable private final Set<V> mModifies;

  /**
   * Creates a new contract that does not have a "modifies" clause, i.e., the contract specifies
   * that the procedure may arbitrarily modify global state as long as it satisfies the "ensures"
   * clause.
   *
   * @param procedure The procedure for which a contract is being created
   * @param requires The "requires" clause. A value of {@code null} represents a trivial clause,
   *     i.e., the logical formula {@code true}.
   * @param ensures The "ensures" clause. A value of {@code null} represents a trivial clause, i.e.,
   *     the logical formula {@code true}.
   */
  public ProcedureContract(final String procedure, final E requires, final E ensures) {
    mProcedure = Objects.requireNonNull(procedure);
    mRequires = requires;
    mEnsures = ensures;
    mModifies = null;
  }

  /**
   * Creates a new contract with a "modifies" clause, i.e., the contract specifies that the
   * procedure may only modify the given global variables.
   *
   * @param procedure The procedure for which a contract is being created
   * @param requires The "requires" clause. A value of {@code null} represents a trivial clause,
   *     i.e., the logical formula {@code true}.
   * @param ensures The "ensures" clause. A value of {@code null} represents a trivial clause, i.e.,
   *     the logical formula {@code true}.
   * @param modifies The set of global variables modifiable by the procedure.
   */
  public ProcedureContract(
      final String procedure, final E requires, final E ensures, final Set<V> modifies) {
    mProcedure = Objects.requireNonNull(procedure);
    mRequires = requires;
    mEnsures = ensures;
    mModifies = Objects.requireNonNull(modifies);
  }

  public boolean hasModifies() {
    return mModifies != null;
  }

  public String getProcedure() {
    return mProcedure;
  }

  public E getRequires() {
    return mRequires;
  }

  public E getEnsures() {
    return mEnsures;
  }

  public Set<V> getModifies() {
    return Collections.unmodifiableSet(mModifies);
  }

  /**
   * Determines whether both the "requires" and "ensures" clauses of the contract are {@code null},
   * i.e., represent the logical formula {@code true}, and the contract does not have a "modifies"
   * clause.
   *
   * <p>Note that this does not mean that the entire contract is trivial in the sense that any
   * procedure would satisfy it, as a "requires" clause of {@code true} indicates that there can be
   * no assertion failure during execution of the procedure for any input or initial global state.
   * An entirely trivial contract would thus instead need to have a "requires" clause {@code false}.
   *
   * <p>For contracts with "modifies" clauses this method always return {@code false} as there is no
   * way to determine if the "modifies" clause is trivial without knowing the entire set of global
   * variables in the program: only when every variable can be modified, the clause would be
   * trivial.
   */
  public boolean hasOnlyTrivialClauses() {
    return mRequires == null && mEnsures == null && !hasModifies();
  }
}
