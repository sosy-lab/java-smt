// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.getSinglePrecisionFloatingPointType;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.assertUsing;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.truth.Truth;
import java.util.Collection;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.TestInfo;
import org.junit.jupiter.params.Parameter;
import org.junit.jupiter.params.ParameterizedClass;
import org.junit.jupiter.params.provider.EnumSource;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.converters.FileTypeConverter;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormula;
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
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/**
 * Base class with helpful utilities for writing tests that use an SMT solver. It instantiates and
 * closes the SMT solver before and after each test, and provides fields with direct access to the
 * most relevant instances.
 *
 * <p>To run the tests using all available solvers, use {@link ParameterizedSolverBasedTest}, or
 * parametrize the class yourself:
 *
 * <pre>
 * {@literal @}ParameterizedClass
 * {@literal @}MethodSource("getAllSolvers")
 *  public static class Test extends SolverBasedTest {
 *    static Solvers[] getAllSolvers() {
 *      return Solvers.values();
 *    }
 *
 *   {@literal @}Parameter public Solvers solver;
 *
 *   {@literal @}Override
 *    protected Solvers solverToUse() {
 *      return solver;
 *    }
 *  }
 * </pre>
 *
 * In your tests {@link #assertThatFormula(BooleanFormula)} can be used to easily write assertions
 * about formulas using Truth.
 *
 * <p>Test that rely on a theory that not all solvers support should call one of the {@code require}
 * methods at the beginning.
 */
public class SolverBasedTest {
  private TestInfo testInfo;

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
  protected @Nullable SLFormulaManager slmgr;
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

  protected ConfigurationBuilder createTestConfigBuilder() throws InvalidConfigurationException {
    ConfigurationBuilder newConfig =
        Configuration.builder().setOption("solver.solver", solverToUse().toString());

    if (enableTracing()) {
      String tracefile =
          "traces/%s/trace_%s_%s.java"
              .formatted(
                  this.getClass().getSimpleName(), testInfo.getDisplayName(), System.nanoTime());
      newConfig.setOption("solver.trace", "true").setOption("solver.tracefile", tracefile);
      FileTypeConverter fileTypeConverter =
          FileTypeConverter.create(Configuration.defaultConfiguration());
      Configuration.getDefaultConverters().put(FileOption.class, fileTypeConverter);
      newConfig.addConverter(PathTemplate.class, fileTypeConverter);
    }

    if (solverToUse() == Solvers.OPENSMT) {
      newConfig.setOption("solver.opensmt.logic", logicToUse().toString());
    }

    return newConfig;
  }

  /**
   * Determines whether execution tracing is enabled for the test suite.
   *
   * <p>Tracing is <b>disabled by default</b> for the following reasons:
   *
   * <ul>
   *   <li><b>Compatibility:</b> Some solvers lack support for tracing-related operations, such as
   *       formula visitation or BitVector-to-Integer conversion.
   *   <li><b>Isolation:</b> Tracing can alter memory pressure or formula allocation patterns,
   *       potentially causing non-deterministic behavior or masking bugs.
   *   <li><b>Performance:</b> Enabling tracing may increase execution time and complicate the
   *       debugging process.
   * </ul>
   *
   * <p>To enable tracing, override this method in your test class to return {@code true}. The
   * produced trace will be stored in the "output/traces" directory with a filename pattern of
   * "trace_[TestClassName]_[TestMethodName]_[Timestamp].java".
   *
   * @return {@code true} if tracing should be enabled; {@code false} otherwise.
   */
  protected boolean enableTracing() {
    return false;
  }

  @BeforeEach
  public final void initSolver(TestInfo info) throws InvalidConfigurationException {
    testInfo = info;
    config = createTestConfigBuilder().build();

    factory = new SolverContextFactory(config, logger, shutdownNotifierToUse());
    context = newContext();

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
    try {
      slmgr = mgr.getSLFormulaManager();
    } catch (UnsupportedOperationException e) {
      slmgr = null;
    }
  }

  @SuppressWarnings("resources")
  protected SolverContext newContext() throws InvalidConfigurationException {
    try {
      return factory.generateContext();
    } catch (InvalidConfigurationException e) {
      assume()
          .withMessage(e.getMessage())
          .that(e)
          .hasCauseThat()
          .isNotInstanceOf(UnsatisfiedLinkError.class);
      throw e;
    }
  }

  @AfterEach
  public final void closeSolver() {
    if (context != null) {
      context.close();
    }
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

  protected final void requireRationalFloor() {
    assume()
        .withMessage("Solver %s does not support floor for rationals", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
    assume()
        .withMessage(
            "Solver %s does not support floor for rationals (random segfaults on ARM64)",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3_WITH_INTERPOLATION);
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

  @SuppressWarnings("CheckReturnValue")
  protected final void requireFPToBitvector() {
    requireFloats();
    try {
      fpmgr.toIeeeBitvector(fpmgr.makeNumber(0, getSinglePrecisionFloatingPointType()));
    } catch (UnsupportedOperationException e) {
      assume()
          .withMessage("Solver %s does not yet support FP-to-BV conversion", solverToUse())
          .that(solverToUse())
          .isNull();
    }
  }

  /** Skip test if the solver does not support quantifiers. */
  protected final void requireQuantifiers() {
    assume()
        .withMessage("Solver %s does not support quantifiers", solverToUse())
        .that(qmgr)
        .isNotNull();
  }

  @SuppressWarnings("unused")
  protected final void requireQuantifierElimination() {
    requireQuantifiers();
    assume()
        .withMessage("Solver %s does not support quantifier elimination", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.BOOLECTOR, Solvers.MATHSAT5, Solvers.YICES2, Solvers.BITWUZLA);
  }

  /** Skip test if the solver does not support arrays. */
  protected final void requireArrays() {
    assume()
        .withMessage("Solver %s does not support the theory of arrays", solverToUse())
        .that(amgr)
        .isNotNull();
  }

  /** Skip test if the solver does not support constant arrays. */
  protected final void requireConstArrays() {
    assume()
        .withMessage("Solver %s does not support constant arrays", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);
  }

  /** Skip test if the solver does not support floats. */
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

  protected final void requireSeparationLogic() {
    assume()
        .withMessage("Solver %s does not support the theory of separation logic", solverToUse())
        .that(slmgr)
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
  }

  protected void requireParser() {
    assume()
        .withMessage("Solver %s does not support parsing formulae", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.BOOLECTOR, Solvers.YICES2);

    assume()
        .withMessage(
            "Solver %s segfaults when parsing short queries or reports invalid length",
            solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3_WITH_INTERPOLATION);
  }

  protected void requireArrayModel() {
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
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  protected void requireUnsatCoreOverAssumptions() {
    assume()
        .withMessage("Solver %s does not support unsat core generation", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.OPENSMT, Solvers.PRINCESS, Solvers.BOOLECTOR, Solvers.CVC4, Solvers.CVC5);
  }

  protected void requireSubstitution() {
    assume()
        .withMessage("Solver %s does not support formula substitution", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  protected void requireUserPropagators() {
    assume()
        .withMessage("Solver %s does not support user propagation", solverToUse())
        .that(solverToUse())
        .isEqualTo(Solvers.Z3);
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
        if (formula instanceof BooleanFormula booleanFormula) {
          Truth.assertThat(m.evaluate(booleanFormula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof IntegerFormula integerFormula) {
          Truth.assertThat(m.evaluate(integerFormula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof RationalFormula rationalFormula) {
          Truth.assertThat(m.evaluate(rationalFormula)).isIn(possibleExpectedValues);
          // assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else if (formula instanceof StringFormula stringFormula) {
          Truth.assertThat(m.evaluate(stringFormula)).isIn(possibleExpectedValues);
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        } else {
          Truth.assertThat(m.evaluate(formula)).isIn(possibleExpectedValues);
        }

        // let's try to check evaluations. Actually the whole method is based on some default values
        // in the solvers, because we do not use constraints for the evaluated formulas.
        Formula eval = m.eval(formula);
        if (eval != null) {
          switch (solverToUse()) {
            case Z3, Z3_WITH_INTERPOLATION -> {
              // ignore, Z3 provides arbitrary values
            }
            case BOOLECTOR -> {
              // ignore, Boolector provides no useful values
            }
            default -> Truth.assertThat(eval).isIn(possibleExpectedFormulas);
          }
        }
      }
    }
  }

  private static final int BITSIZE = 32;

  protected Formula makeVariable(String name) {
    return imgr == null ? bvmgr.makeVariable(BITSIZE, name) : imgr.makeVariable(name);
  }

  protected Formula makeNumber(int number) {
    return imgr == null ? bvmgr.makeBitvector(BITSIZE, number) : imgr.makeNumber(number);
  }

  protected Formula addNumber(Formula x, Formula y) {
    if (x instanceof IntegerFormula xInt && y instanceof IntegerFormula yInt) {
      return imgr.add(xInt, yInt);
    }
    if (x instanceof BitvectorFormula xBv && y instanceof BitvectorFormula yBv) {
      return bvmgr.add(xBv, yBv);
    }
    throw new IllegalArgumentException();
  }

  protected Formula multiplyNumber(Formula x, Formula y) {
    if (x instanceof IntegerFormula xInt && y instanceof IntegerFormula yInt) {
      return imgr.multiply(xInt, yInt);
    }
    if (x instanceof BitvectorFormula xBv && y instanceof BitvectorFormula yBv) {
      return bvmgr.multiply(xBv, yBv);
    }
    throw new IllegalArgumentException();
  }

  protected BooleanFormula lessThanNumber(Formula x, Formula y) {
    if (x instanceof IntegerFormula xInt && y instanceof IntegerFormula yInt) {
      return imgr.lessThan(xInt, yInt);
    }
    if (x instanceof BitvectorFormula xBv && y instanceof BitvectorFormula yBv) {
      return bvmgr.lessThan(xBv, yBv, true);
    }
    throw new IllegalArgumentException();
  }

  protected BooleanFormula greaterThanNumber(Formula x, Formula y) {
    if (x instanceof IntegerFormula xInt && y instanceof IntegerFormula yInt) {
      return imgr.greaterThan(xInt, yInt);
    }
    if (x instanceof BitvectorFormula xBv && y instanceof BitvectorFormula yBv) {
      return bvmgr.greaterThan(xBv, yBv, true);
    }
    throw new IllegalArgumentException();
  }

  @ParameterizedClass
  @EnumSource(Solvers.class)
  public abstract static class ParameterizedSolverBasedTest extends SolverBasedTest {
    @Parameter public Solvers solver;

    @Override
    protected Solvers solverToUse() {
      return solver;
    }
  }
}
