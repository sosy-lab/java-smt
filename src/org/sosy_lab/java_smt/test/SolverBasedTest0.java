// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.assertUsing;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.truth.Truth;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.Collection;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.After;
import org.junit.Before;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/**
 * Abstract base class with helpful utilities for writing tests that use an SMT solver. It
 * instantiates and closes the SMT solver before and after each test, and provides fields with
 * direct access to the most relevant instances.
 *
 * <p>To run the tests using all available solvers, add the following code to your class:
 *
 * <pre>
 * <code>
 *  {@literal @}Parameters(name="{0}")
 *  public static List{@literal <Object[]>} getAllSolvers() {
 *    return allSolversAsParameters();
 *  }
 *
 *  {@literal @}Parameter(0)
 *  public Solvers solver;
 *
 *  {@literal @}Override
 *  protected Solvers solverToUse() {
 *    return solver;
 *  }
 * </code>
 * </pre>
 *
 * {@link #assertThatFormula(BooleanFormula)} can be used to easily write assertions about formulas
 * using Truth.
 *
 * <p>Test that rely on a theory that not all solvers support should call one of the {@code require}
 * methods at the beginning.
 */
@SuppressFBWarnings(value = "URF_UNREAD_PUBLIC_OR_PROTECTED_FIELD", justification = "test code")
public abstract class SolverBasedTest0 {

  protected Configuration config;
  protected final LogManager logger = LogManager.createTestLogManager();

  protected SolverContextFactory factory;
  protected SolverContext context;
  protected FormulaManager mgr;
  protected BooleanFormulaManager bmgr;
  protected UFManager fmgr;
  protected IntegerFormulaManager imgr;
  protected @Nullable RationalFormulaManager rmgr;
  protected @Nullable BitvectorFormulaManager bvmgr;
  protected @Nullable QuantifiedFormulaManager qmgr;
  protected @Nullable ArrayFormulaManager amgr;
  protected @Nullable FloatingPointFormulaManager fpmgr;
  protected @Nullable StringFormulaManager smgr;
  protected @Nullable EnumerationFormulaManager emgr;
  protected ShutdownManager shutdownManager = ShutdownManager.create();

  protected ShutdownNotifier shutdownNotifierToUse() {
    return shutdownManager.getNotifier();
  }

  /**
   * Return the solver to use in this test. The default is SMTInterpol because it's the only solver
   * guaranteed on all platforms. Overwrite to specify a different solver.
   */
  protected Solvers solverToUse() {
    return Solvers.SMTINTERPOL;
  }

  /** This method is only called, if OpenSMT is called. OpenSMT needs to know the logic upfront. */
  protected Logics logicToUse() {
    return Logics.QF_AUFLIRA;
  }

  protected ConfigurationBuilder createTestConfigBuilder() {
    ConfigurationBuilder newConfig =
        Configuration.builder().setOption("solver.solver", solverToUse().toString());
    if (solverToUse() == Solvers.OPENSMT) {
      newConfig.setOption("solver.opensmt.logic", logicToUse().toString());
    }
    if (solverToUse() == Solvers.PRINCESS) {
      newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
      newConfig.setOption("solver.useBinary", String.valueOf(true));
    }
    if (solverToUse() == Solvers.SOLVERLESS){
      newConfig.setOption("solver.generateSMTLIB2", String.valueOf(true));
    }
    return newConfig;
  }

  @Before
  public final void initSolver() throws InvalidConfigurationException {
    config = createTestConfigBuilder().build();

    factory = new SolverContextFactory(config, logger, shutdownNotifierToUse());
    try {
      context = factory.generateContext();
    } catch (InvalidConfigurationException e) {
      assume()
          .withMessage(e.getMessage())
          .that(e)
          .hasCauseThat()
          .isNotInstanceOf(UnsatisfiedLinkError.class);
      throw e;
    }
    mgr = context.getFormulaManager();

    fmgr = mgr.getUFManager();
    bmgr = mgr.getBooleanFormulaManager();
    // Needed for Boolector tests (Does not support Integer Formulas)
    try {
      imgr = mgr.getIntegerFormulaManager();
    } catch (UnsupportedOperationException e) {
      imgr = null;
    }
    try {
      rmgr = mgr.getRationalFormulaManager();
    } catch (UnsupportedOperationException e) {
      rmgr = null;
    }
    try {
      bvmgr = mgr.getBitvectorFormulaManager();
    } catch (UnsupportedOperationException e) {
      bvmgr = null;
    }
    try {
      qmgr = mgr.getQuantifiedFormulaManager();
    } catch (UnsupportedOperationException e) {
      qmgr = null;
    }
    try {
      amgr = mgr.getArrayFormulaManager();
    } catch (UnsupportedOperationException e) {
      amgr = null;
    }
    try {
      fpmgr = mgr.getFloatingPointFormulaManager();
    } catch (UnsupportedOperationException e) {
      fpmgr = null;
    }
    try {
      smgr = mgr.getStringFormulaManager();
    } catch (UnsupportedOperationException e) {
      smgr = null;
    }
    try {
      emgr = mgr.getEnumerationFormulaManager();
    } catch (UnsupportedOperationException e) {
      emgr = null;
    }
    if (Generator.isLoggingEnabled()) {
      Generator.resetGenerator();
    }
  }

  @After
  public final void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  /** Skip test if the solver does not support Booleans in UFs. */
  protected final void requireBooleanUFs() {
    assume()
        .withMessage(
            "Solver %s does not support making UFs with Boolean return values", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.MATHSAT5);
  }

  /** Skip test if the solver does not support Booleans as arguments in Arrays. */
  protected final void requireBooleanArgumentArrays() {
    assume()
        .withMessage(
            "Solver %s does not support making Arrays with Bool as arguments", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.MATHSAT5, Solvers.SMTINTERPOL);
  }

  /** Skip test if the solver does not support any other sort than bitvector in Arrays. */
  protected final void requireAllSortArrays() {
    assume()
        .withMessage(
            "Solver %s does not support making Arrays with sorts other than bitvectors",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  /** Skip test if the solver does not support UFs without arguments. */
  protected final void requireNoArgumentsInUFs() {
    assume()
        .withMessage("Solver %s does not support making UFs without input Arguments", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  /** Skip test if the solver does not support integers. */
  protected final void requireIntegers() {
    assume()
        .withMessage("Solver %s does not support the theory of integers", solverToUse())
        .that(imgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support rationals. */
  protected final void requireRationals() {
    assume()
        .withMessage("Solver %s does not support the theory of rationals", solverToUse())
        .that(rmgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support bitvectors. */
  protected final void requireBitvectors() {
    assume()
        .withMessage("Solver %s does not support the theory of bitvectors", solverToUse())
        .that(bvmgr)
        .isNotNull();
  }

  protected final void requireBitvectorToInt() {
    assume()
        .withMessage(
            "Solver %s does not yet support the conversion between bitvectors and integers",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.YICES2);
  }

  /** Skip test if the solver does not support quantifiers. */
  protected final void requireQuantifiers() {
    assume()
        .withMessage("Solver %s does not support quantifiers", solverToUse())
        .that(qmgr)
        .isNotNull();
    // FIXME: Disabled while we're testing the binary backend
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
  }

  /** Skip test if the solver does not support arrays. */
  protected /*final*/ void requireArrays() {
    assume()
        .withMessage("Solver %s does not support the theory of arrays", solverToUse())
        .that(amgr)
        .isNotNull();
  }

  protected final void requireFloats() {
    assume()
        .withMessage("Solver %s does not support the theory of floats", solverToUse())
        .that(fpmgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support strings. */
  protected final void requireStrings() {
    assume()
        .withMessage("Solver %s does not support the theory of strings", solverToUse())
        .that(smgr)
        .isNotNull();
    assume()
        .withMessage("Solver %s does not support the theory of arrays", solverToUse())
        .that(amgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support enumeration theory. */
  protected final void requireEnumeration() {
    assume()
        .withMessage("Solver %s does not support the theory of enumerations", solverToUse())
        .that(emgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support optimization. */
  protected final void requireOptimization() {
    try {
      context.newOptimizationProverEnvironment().close();
    } catch (UnsupportedOperationException e) {
      assume()
          .withMessage("Solver %s does not support optimization", solverToUse())
          .that(e)
          .isNull();
    }
  }

  protected final void requireInterpolation() {
    try {
      context.newProverEnvironmentWithInterpolation().close();
    } catch (UnsupportedOperationException e) {
      assume()
          .withMessage("Solver %s does not support interpolation", solverToUse())
          .that(e)
          .isNull();
    }
    // FIXME: Disabled while we're testing the binary backend
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
  }

  protected void requireParser() {
    assume()
        .withMessage("Solver %s does not support parsing formulae", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.YICES2, Solvers.CVC5);
    // FIXME: Disabled while we're testing the binary backend
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
  }

  protected void requireArrayModel() {
    // INFO: OpenSmt does not support model generation for array
    assume()
        .withMessage("Solver %s does not support model generation for arrays", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
  }

  protected void requireModel() {
    /*assume()
    .withMessage("Solver %s does not support model generation in a usable way", solverToUse())
    .that(solverToUse())
    .isNotEqualTo(Solvers.BOOLECTOR);*/
  }

  protected void requireVisitor() {
    assume()
        .withMessage("Solver %s does not support formula visitor", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  protected void requireUnsatCore() {
    assume()
        .withMessage("Solver %s does not support unsat core generation", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.BOOLECTOR, Solvers.OPENSMT);
    // FIXME: Disabled while testing Princess binary backend
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);
  }

  protected void requireSubstitution() {
    assume()
        .withMessage("Solver %s does not support formula substitution", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  /**
   * Use this for checking assertions about BooleanFormulas with Truth: <code>
   * assertThatFormula(formula).is...()</code>.
   */
  protected final BooleanFormulaSubject assertThatFormula(BooleanFormula formula) {
    return assertUsing(context).that(formula);
  }

  /**
   * Use this for checking assertions about ProverEnvironments with Truth: <code>
   * assertThatEnvironment(stack).is...()</code>.
   *
   * <p>For new code, we suggest using {@link
   * ProverEnvironmentSubject#assertThat(BasicProverEnvironment)} with a static import.
   */
  protected final ProverEnvironmentSubject assertThatEnvironment(BasicProverEnvironment<?> prover) {
    return assertThat(prover);
  }

  protected void evaluateInModel(
      BooleanFormula constraint,
      Formula formula,
      Collection<Object> possibleExpectedValues,
      Collection<Formula> possibleExpectedFormulas)
      throws SolverException, InterruptedException {

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(constraint);
      assertThat(prover).isSatisfiable();

      try (Model m = prover.getModel()) {
        if (formula instanceof BooleanFormula) {
          Truth.assertThat(m.evaluate((BooleanFormula) formula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof IntegerFormula) {
          Truth.assertThat(m.evaluate((IntegerFormula) formula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof RationalFormula) {
          Truth.assertThat(m.evaluate((RationalFormula) formula)).isIn(possibleExpectedValues);
          // assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof StringFormula) {
          Truth.assertThat(m.evaluate((StringFormula) formula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else {
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        }

        // let's try to check evaluations. Actually the whole method is based on some default values
        // in the solvers, because we do not use constraints for the evaluated formulas.
        Formula eval = m.eval(formula);
        if (eval != null) {
          switch (solverToUse()) {
            case Z3:
              // ignore, Z3 provides arbitrary values
              break;
            case BOOLECTOR:
              // ignore, Boolector provides no useful values
              break;
            default:
              Truth.assertThat(eval).isIn(possibleExpectedFormulas);
          }
        }
      }
    }
  }

  @RunWith(Parameterized.class)
  public abstract static class ParameterizedSolverBasedTest0 extends SolverBasedTest0 {

    @Parameters(name = "{0}")
    public static Object[] getAllSolvers() {
      return Solvers.values();
    }

    @Parameter(0)
    public Solvers solver;

    @Override
    protected Solvers solverToUse() {
      return solver;
    }
  }
}
