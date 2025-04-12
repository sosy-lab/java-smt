// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Function;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultBooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private static final ImmutableList<String> NAMES =
      ImmutableList.of(
          "java-smt",
          "JavaSMT",
          "sosylab",
          "test",
          "foo",
          "bar",
          "baz",
          "declare",
          "exit",
          "(exit)",
          "!=",
          "~",
          ",",
          ".",
          ":",
          " ",
          "  ",
          "(",
          ")",
          "[",
          "]",
          "{",
          "}",
          "[]",
          "\"",
          "\"\"",
          "\"\"\"",
          // TODO next line is disabled because of a problem in MathSAT5 (version 5.6.3).
          // "'", "''", "'''",
          "\n",
          "\t",
          "\u0000",
          "\u0001",
          "\u1234",
          "\u2e80",
          " this is a quoted symbol ",
          " so is \n  this one ",
          " \" can occur too ",
          " af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984");

  private static final ImmutableSet<String> FURTHER_SMTLIB2_KEYWORDS =
      ImmutableSet.of(
          "let",
          "forall",
          "exists",
          "match",
          "Bool",
          "continued-execution",
          "error",
          "immediate-exit",
          "incomplete",
          "logic",
          "memout",
          "sat",
          "success",
          "theory",
          "unknown",
          "unsupported",
          "unsat",
          "_",
          "as",
          "BINARY",
          "DECIMAL",
          "HEXADECIMAL",
          "NUMERAL",
          "par",
          "STRING",
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option");

  /**
   * Some special chars are not allowed to appear in symbol names. See {@link
   * AbstractFormulaManager#DISALLOWED_CHARACTERS}.
   */
  @SuppressWarnings("javadoc")
  private static final ImmutableSet<String> UNSUPPORTED_NAMES =
      ImmutableSet.of(
          "|",
          "||",
          "|||",
          "|test",
          "|test|",
          "t|e|s|t",
          "\\",
          "\\s",
          "\\|\\|",
          "| this is a quoted symbol |",
          "| so is \n  this one |",
          "| \" can occur too |",
          "| af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984|");

  protected List<String> getAllNames() {
    return ImmutableList.<String>builder()
        .addAll(NAMES)
        .addAll(AbstractFormulaManager.BASIC_OPERATORS)
        .addAll(AbstractFormulaManager.SMTLIB2_KEYWORDS)
        .addAll(AbstractFormulaManager.DISALLOWED_CHARACTER_REPLACEMENT.values())
        .addAll(FURTHER_SMTLIB2_KEYWORDS)
        .addAll(UNSUPPORTED_NAMES)
        .build();
  }

  boolean allowInvalidNames() {
    return true;
  }

  @CanIgnoreReturnValue
  private <T extends Formula> T createVariableWith(Function<String, T> creator, String name) {
    if (allowInvalidNames() && !mgr.isValidName(name)) {
      assertThrows(IllegalArgumentException.class, () -> creator.apply(name));
      return null;
    } else {
      return creator.apply(name);
    }
  }

  private <T extends Formula> void testName0(
      String name, Function<String, T> creator, BiFunction<T, T, BooleanFormula> eq, boolean isUF)
      throws SolverException, InterruptedException {
    requireVisitor();

    // create a variable
    T var = createVariableWith(creator, name);
    if (var == null) {
      return;
    }

    // check whether it exists with the given name
    Map<String, Formula> map = mgr.extractVariables(var);
    if (isUF) {
      assertThat(map).isEmpty();
      map = mgr.extractVariablesAndUFs(var);
    }
    assertThat(map).hasSize(1);
    assertThat(map).containsEntry(name, var);

    // check whether we can create the same variable again
    T var2 = createVariableWith(creator, name);
    if (var2 == null) {
      return;
    }

    // for simple formulas, we can expect a direct equality
    // (for complex formulas this is not satisfied)
    assertThat(var2).isEqualTo(var);
    assertThat(var2.toString()).isEqualTo(var.toString());
    assertThatFormula(eq.apply(var, var2)).isSatisfiable();
    if (var instanceof FloatingPointFormula) {
      // special case: NaN != NaN
      assertThatFormula(bmgr.not(eq.apply(var, var2))).isSatisfiable();
    } else {
      assertThatFormula(bmgr.not(eq.apply(var, var2))).isUnsatisfiable();
      assertThatFormula(eq.apply(var, var2)).isSatisfiableAndHasModel(1);
    }

    // check whether SMTLIB2-dump is possible
    @SuppressWarnings("unused")
    String dump = mgr.dumpFormula(eq.apply(var, var)).toString();

    if (allowInvalidNames()) {
      // try to create a new (!) variable with a different name, the escaped previous name.
      assertThat(createVariableWith(creator, "|" + name + "|")).isEqualTo(null);
    }
  }

  @Test
  public void testBoolVariable() {
    for (String name : getAllNames()) {
      createVariableWith(bmgr::makeVariable, name);
    }
  }

  @Test
  public void testNameBool() throws SolverException, InterruptedException {
    for (String name : getAllNames()) {
      testName0(name, bmgr::makeVariable, bmgr::equivalence, false);
    }
  }

  @Test
  public void testNameInt() throws SolverException, InterruptedException {
    requireIntegers();
    for (String name : getAllNames()) {
      testName0(name, imgr::makeVariable, imgr::equal, false);
    }
  }

  @Test
  public void testNameRat() throws SolverException, InterruptedException {
    requireRationals();
    for (String name : getAllNames()) {
      testName0(name, rmgr::makeVariable, rmgr::equal, false);
    }
  }

  @Test
  public void testNameBV() throws SolverException, InterruptedException {
    requireBitvectors();
    for (String name : getAllNames()) {
      testName0(name, s -> bvmgr.makeVariable(4, s), bvmgr::equal, false);
    }
  }

  @Test
  public void testNameFloat() throws SolverException, InterruptedException {
    requireFloats();
    for (String name : getAllNames()) {
      testName0(
          name,
          s -> fpmgr.makeVariable(s, FormulaType.getSinglePrecisionFloatingPointType()),
          fpmgr::equalWithFPSemantics,
          false);
    }
  }

  @Test
  public void testNameIntArray() throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    for (String name : getAllNames()) {
      testName0(name, s -> amgr.makeArray(s, IntegerType, IntegerType), amgr::equivalence, false);
    }
  }

  @Test
  public void testNameBvArray() throws SolverException, InterruptedException {
    requireBitvectors();
    requireArrays();
    // Someone who knows princess has to debug this!
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
    for (String name : NAMES) {
      testName0(
          name,
          s ->
              amgr.makeArray(
                  s,
                  FormulaType.getBitvectorTypeWithSize(2),
                  FormulaType.getBitvectorTypeWithSize(2)),
          amgr::equivalence,
          false);
    }
  }

  @Test
  public void testNameUF1Bool() throws SolverException, InterruptedException {
    requireIntegers();
    for (String name : NAMES) {
      testName0(
          name,
          s -> fmgr.declareAndCallUF(s, BooleanType, imgr.makeNumber(0)),
          bmgr::equivalence,
          true);
    }
  }

  @Test
  public void testNameUF1Int() throws SolverException, InterruptedException {
    requireIntegers();
    for (String name : NAMES) {
      testName0(
          name, s -> fmgr.declareAndCallUF(s, IntegerType, imgr.makeNumber(0)), imgr::equal, true);
    }
  }

  @Test
  public void testNameUFBv() throws SolverException, InterruptedException {
    requireBitvectors();
    // Someone who knows princess has to debug this!
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
    for (String name : getAllNames()) {
      testName0(
          name,
          s -> fmgr.declareAndCallUF(s, BooleanType, bvmgr.makeBitvector(2, 0)),
          bmgr::equivalence,
          true);
    }
  }

  @Test
  public void testNameUF2Bool() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula zero = imgr.makeNumber(0);
    for (String name : NAMES) {
      testName0(
          name, s -> fmgr.declareAndCallUF(s, BooleanType, zero, zero), bmgr::equivalence, true);
    }
  }

  @Test
  public void testNameUF2Int() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula zero = imgr.makeNumber(0);
    for (String name : NAMES) {
      testName0(name, s -> fmgr.declareAndCallUF(s, IntegerType, zero, zero), imgr::equal, true);
    }
  }

  @Test
  public void testNameInQuantification() {
    requireQuantifiers();
    requireIntegers();

    for (String name : getAllNames()) {

      IntegerFormula var = createVariableWith(imgr::makeVariable, name);
      if (var == null) {
        continue;
      }
      IntegerFormula zero = imgr.makeNumber(0);
      BooleanFormula eq = imgr.equal(var, zero);
      BooleanFormula exists = qmgr.exists(var, eq);
      BooleanFormula query = bmgr.and(bmgr.not(eq), exists);

      // (var != 0) & (EX var: (var == 0))

      assertThat(mgr.extractVariablesAndUFs(eq)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(eq)).containsEntry(name, var);

      assertThat(mgr.extractVariablesAndUFs(query)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(query)).containsEntry(name, var);

      assertThat(mgr.extractVariablesAndUFs(exists)).isEmpty();

      mgr.visit(
          query,
          new DefaultFormulaVisitor<Void>() {

            @Override
            public Void visitQuantifier(
                BooleanFormula pF,
                Quantifier pQuantifier,
                List<Formula> pBoundVariables,
                BooleanFormula pBody) {
              if (solverToUse() != Solvers.PRINCESS) {
                // TODO Princess does not (yet) return quantified variables.
                assertThat(pBoundVariables).hasSize(1);
              }
              for (Formula f : pBoundVariables) {
                Map<String, Formula> map = mgr.extractVariables(f);
                assertThat(map).hasSize(1);
                assertThat(map).containsEntry(name, f);
              }
              return null;
            }

            @Override
            protected Void visitDefault(Formula pF) {
              return null;
            }
          });
    }
  }

  @Test
  public void testNameInNestedQuantification() {
    requireQuantifiers();
    requireIntegers();

    for (String name : getAllNames()) {

      IntegerFormula var1 = createVariableWith(imgr::makeVariable, name + 1);
      if (var1 == null) {
        continue;
      }
      IntegerFormula var2 = createVariableWith(imgr::makeVariable, name + 2);
      IntegerFormula var3 = createVariableWith(imgr::makeVariable, name + 3);
      IntegerFormula var4 = createVariableWith(imgr::makeVariable, name + 4);
      IntegerFormula zero = imgr.makeNumber(0);

      // (v1 == 0) & (EX v2: ((v2 == v1) & (EX v3: ((v3 == v2) & (EX v4: (v4 == v3))))

      BooleanFormula eq01 = imgr.equal(zero, var1);
      BooleanFormula eq12 = imgr.equal(var1, var2);
      BooleanFormula eq23 = imgr.equal(var2, var3);
      BooleanFormula eq34 = imgr.equal(var3, var4);
      BooleanFormula exists4 = qmgr.exists(var4, eq34);
      BooleanFormula exists3 = qmgr.exists(var3, bmgr.and(eq23, exists4));
      BooleanFormula exists2 = qmgr.exists(var2, bmgr.and(eq12, exists3));
      BooleanFormula query = bmgr.and(eq01, exists2);

      assertThat(mgr.extractVariablesAndUFs(eq01)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(eq01)).containsEntry(name + 1, var1);

      assertThat(mgr.extractVariablesAndUFs(eq12)).hasSize(2);
      assertThat(mgr.extractVariablesAndUFs(eq12)).containsEntry(name + 1, var1);
      assertThat(mgr.extractVariablesAndUFs(eq12)).containsEntry(name + 2, var2);

      assertThat(mgr.extractVariablesAndUFs(eq23)).hasSize(2);
      assertThat(mgr.extractVariablesAndUFs(eq23)).containsEntry(name + 2, var2);
      assertThat(mgr.extractVariablesAndUFs(eq23)).containsEntry(name + 3, var3);

      assertThat(mgr.extractVariablesAndUFs(eq34)).hasSize(2);
      assertThat(mgr.extractVariablesAndUFs(eq34)).containsEntry(name + 3, var3);
      assertThat(mgr.extractVariablesAndUFs(eq34)).containsEntry(name + 4, var4);

      assertThat(mgr.extractVariablesAndUFs(query)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(query)).containsEntry(name + 1, var1);

      assertThat(mgr.extractVariablesAndUFs(exists2)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(exists2)).containsEntry(name + 1, var1);

      assertThat(mgr.extractVariablesAndUFs(exists3)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(exists3)).containsEntry(name + 2, var2);

      assertThat(mgr.extractVariablesAndUFs(exists4)).hasSize(1);
      assertThat(mgr.extractVariablesAndUFs(exists4)).containsEntry(name + 3, var3);

      mgr.visit(
          query,
          new DefaultFormulaVisitor<Void>() {

            int depth = 1;

            @Override
            public Void visitQuantifier(
                BooleanFormula pF,
                Quantifier pQuantifier,
                List<Formula> pBoundVariables,
                BooleanFormula pBody) {
              if (solverToUse() != Solvers.PRINCESS) {
                // TODO Princess does not return quantified variables.
                assertThat(pBoundVariables).hasSize(1);
              }
              for (Formula f : pBoundVariables) {
                Map<String, Formula> map = mgr.extractVariables(f);
                assertThat(map).hasSize(1);
                assertThat(map).containsEntry(name + depth, f);
              }
              depth++;
              return null;
            }

            @Override
            protected Void visitDefault(Formula pF) {
              return null;
            }
          });
    }
  }

  @Test
  public void testBoolVariableNameInVisitor() {
    requireVisitor();

    for (String name : getAllNames()) {
      BooleanFormula var = createVariableWith(bmgr::makeVariable, name);
      if (var == null) {
        continue;
      }

      bmgr.visit(
          var,
          new DefaultBooleanFormulaVisitor<Void>() {
            @Override
            protected Void visitDefault() {
              throw new AssertionError("unexpected case");
            }

            @Override
            public Void visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> pDecl) {
              assertThat(pDecl.getName()).isEqualTo(name);
              return null;
            }
          });
    }
  }

  @Test
  public void testBoolVariableDump() {
    // FIXME: Broken on yices2
    //  Yices does not quote symbols when dumping a formula, f.ex for the variable "(" we get
    //    (declare-fun |(| () Bool)
    //    (assert ()
    //  which is not a valid SMTLIB script.
    assume().that(solverToUse()).isNotEqualTo(Solvers.YICES2);
    for (String name : getAllNames()) {
      BooleanFormula var = createVariableWith(bmgr::makeVariable, name);
      if (var != null) {
        @SuppressWarnings("unused")
        String dump = mgr.dumpFormula(var).toString();
      }
    }
  }

  @Test
  public void testEqBoolVariableDump() {
    // FIXME: Rewrite test? Most solvers will simplify the formula to `true`.
    for (String name : getAllNames()) {
      BooleanFormula var = createVariableWith(bmgr::makeVariable, name);
      if (var != null) {
        @SuppressWarnings("unused")
        String dump = mgr.dumpFormula(bmgr.equivalence(var, var)).toString();
      }
    }
  }

  @Test
  public void testIntVariable() {
    requireIntegers();
    for (String name : getAllNames()) {
      createVariableWith(imgr::makeVariable, name);
    }
  }

  @Test
  public void testInvalidRatVariable() {
    requireRationals();
    for (String name : getAllNames()) {
      createVariableWith(rmgr::makeVariable, name);
    }
  }

  @Test
  public void testBVVariable() {
    requireBitvectors();
    for (String name : getAllNames()) {
      createVariableWith(v -> bvmgr.makeVariable(4, v), name);
    }
  }

  @Test
  public void testInvalidFloatVariable() {
    requireFloats();
    for (String name : getAllNames()) {
      createVariableWith(
          v -> fpmgr.makeVariable(v, FormulaType.getSinglePrecisionFloatingPointType()), name);
    }
  }

  @Test
  public void testIntArrayVariable() {
    requireArrays();
    requireIntegers();
    for (String name : getAllNames()) {
      createVariableWith(v -> amgr.makeArray(v, IntegerType, IntegerType), name);
    }
  }

  @Test
  public void testBvArrayVariable() {
    requireArrays();
    requireBitvectors();
    // Someone who knows princess has to debug this!
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
    for (String name : getAllNames()) {
      createVariableWith(
          v ->
              amgr.makeArray(
                  v,
                  FormulaType.getBitvectorTypeWithSize(2),
                  FormulaType.getBitvectorTypeWithSize(2)),
          name);
    }
  }

  @Test
  public void sameBehaviorTest() {
    for (String name : getAllNames()) {
      if (mgr.isValidName(name)) {
        // should pass without exception
        AbstractFormulaManager.checkVariableName(name);
      } else {
        assertThrows(
            IllegalArgumentException.class, () -> AbstractFormulaManager.checkVariableName(name));
      }
    }
  }
}
