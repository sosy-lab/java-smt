/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.Sets;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;
import java.util.stream.Stream;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

public class Z3NativeApiTest {
  @BeforeClass
  public static void loadLibraries() {
    NativeLibraries.loadLibrary("z3");
    NativeLibraries.loadLibrary("z3java");

    System.setProperty("z3.skipLibraryLoad", "true");
  }

  private Set<Expr<?>> getFreeVars(Expr<?> expr) {
    Deque<Expr<?>> worklist = new ArrayDeque<>();
    worklist.push(expr);

    Set<Expr<?>> vars = Sets.newHashSet();

    while (!worklist.isEmpty()) {
      Expr<?> f = worklist.removeFirst();
      if (f.isConst()) {
        vars.add(f);
      }
      for (Expr<?> c : f.getArgs()) {
        worklist.addLast(c);
      }
    }
    return vars;
  }

  private Model solveHornClauses(Context env, Expr<BoolSort>... chc) {
    Params opts = env.mkParams();
    opts.add("engine", "spacer");
    opts.add("spacer.order_children", 2);
    opts.add("xform.inline_eager", false);
    opts.add("xform.inline_linear", false);
    opts.add("xform.slice", false);
    opts.add("spacer.max_level", 10);

    Solver solver = env.mkSolver("HORN");
    solver.setParameters(opts);

    solver.add(chc);
    Status status = solver.check();

    assertThat(status).isEqualTo(Status.SATISFIABLE);

    return solver.getModel();
  }

  private Expr<BoolSort> interpolate(Context env, Expr<BoolSort> A, Expr<BoolSort> B) {
    Set<Expr<?>> varsA = getFreeVars(A);
    Set<Expr<?>> varsB = getFreeVars(B);

    Expr<?>[] shared = Sets.intersection(varsA, varsB).toArray(new Expr<?>[0]);
    Sort[] sorts = Stream.of(shared).map(Expr::getSort).toArray(Sort[]::new);

    FuncDecl<BoolSort> symbolItp =
        env.mkFuncDecl(
            "Itp", Stream.of(shared).map(Expr::getSort).toArray(Sort[]::new), env.mkBoolSort());
    Expr<BoolSort> constant = symbolItp.apply(shared);

    Expr<BoolSort> left =
        env.mkForall(
            varsA.toArray(Expr<?>[]::new), env.mkImplies(A, constant), 1, null, null, null, null);

    Expr<BoolSort> right =
        env.mkForall(
            varsB.toArray(Expr<?>[]::new),
            env.mkImplies(constant, env.mkNot(B)),
            1,
            null,
            null,
            null,
            null);

    Model model = solveHornClauses(env, left, right);
    return model.eval(constant, false);
  }

  /** Validate that I is an interpolant for A and B */
  private boolean validate(Context env, Expr<BoolSort> A, Expr<BoolSort> B, Expr<BoolSort> I) {
    Solver solver = env.mkSolver("QF_LIA");
    return solver.check(env.mkNot(env.mkImplies(A, I))).equals(Status.UNSATISFIABLE)
        && solver.check(env.mkNot(env.mkImplies(I, env.mkNot(B)))).equals(Status.UNSATISFIABLE)
        && Sets.intersection(getFreeVars(A), getFreeVars(B)).containsAll(getFreeVars(I));
  }

  @Test
  public void interpolationTest() {
    // Translation of an example by Arie Gurfinkel for calculating interpolants with spacer in Z3
    // See https://github.com/agurfinkel/spacer-on-jupyter/blob/master/Dagstuhl2019.ipynb for the
    // original Python code

    Context env = new Context();

    Expr<IntSort> a = env.mkIntConst("a");
    Expr<IntSort> b = env.mkIntConst("b");
    Expr<IntSort> x = env.mkIntConst("x");

    Expr<BoolSort> A = env.mkAnd(env.mkLt(a, x), env.mkLt(x, b));
    Expr<BoolSort> B = env.mkLt(b, a);

    Expr<BoolSort> I = interpolate(env, A, B);

    assertThat(validate(env, A, B, I)).isTrue();
    env.close();
  }
}
