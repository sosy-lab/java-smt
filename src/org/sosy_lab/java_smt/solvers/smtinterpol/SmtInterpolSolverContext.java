// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap.CopyMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingProverEnvironment;

public final class SmtInterpolSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.smtinterpol")
  private static class SmtInterpolSettings {

    @Option(
        secure = true,
        description =
            "Double check generated results like interpolants and models whether they are correct")
    private boolean checkResults = false;

    @Option(
        secure = true,
        description =
            "Further options that will be set to true for SMTInterpol "
                + "in addition to the default options. Format is 'option1,option2,option3'")
    private List<String> furtherOptions = ImmutableList.of();

    private final @Nullable PathCounterTemplate smtLogfile;

    private final ImmutableMap<String, Object> optionsMap;

    private SmtInterpolSettings(
        Configuration config, long pRandomSeed, @Nullable PathCounterTemplate pSmtLogfile)
        throws InvalidConfigurationException {
      config.inject(this);
      smtLogfile = pSmtLogfile;

      ImmutableMap.Builder<String, Object> opt = ImmutableMap.builder();
      opt.put(":global-declarations", true);
      opt.put(":random-seed", pRandomSeed);

      // We always need to enable the option for interpolation, even if interpolation is not used.
      // Otherwise, using interpolation later does not work.
      opt.put(":produce-interpolants", true);

      if (checkResults) {
        opt.put(":interpolant-check-mode", true);
        opt.put(":unsat-core-check-mode", true);
        opt.put(":model-check-mode", true);
      }
      for (String option : furtherOptions) {
        opt.put(option, true);
      }
      optionsMap = opt.buildOrThrow();
    }
  }

  private final SmtInterpolSettings settings;
  private final ShutdownNotifier shutdownNotifier;
  private final SmtInterpolFormulaManager manager;

  private SmtInterpolSolverContext(
      SmtInterpolFormulaManager pManager,
      ShutdownNotifier pShutdownNotifier,
      SmtInterpolSettings pSettings) {
    super(pManager);
    settings = pSettings;
    shutdownNotifier = checkNotNull(pShutdownNotifier);
    manager = pManager;
  }

  public static SmtInterpolSolverContext create(
      Configuration config,
      LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate smtLogfile,
      long randomSeed,
      NonLinearArithmetic pNonLinearArithmetic)
      throws InvalidConfigurationException {

    SmtInterpolSettings settings = new SmtInterpolSettings(config, randomSeed, smtLogfile);
    Script script = getSmtInterpolScript(pShutdownNotifier, smtLogfile, settings, logger);

    SmtInterpolFormulaCreator creator = new SmtInterpolFormulaCreator(script);
    SmtInterpolUFManager functionTheory = new SmtInterpolUFManager(creator);
    SmtInterpolBooleanFormulaManager booleanTheory = new SmtInterpolBooleanFormulaManager(creator);
    SmtInterpolIntegerFormulaManager integerTheory =
        new SmtInterpolIntegerFormulaManager(creator, pNonLinearArithmetic);
    SmtInterpolRationalFormulaManager rationalTheory =
        new SmtInterpolRationalFormulaManager(creator, pNonLinearArithmetic);
    SmtInterpolArrayFormulaManager arrayTheory = new SmtInterpolArrayFormulaManager(creator);
    SmtInterpolFormulaManager manager =
        new SmtInterpolFormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            arrayTheory,
            logger);
    return new SmtInterpolSolverContext(manager, pShutdownNotifier, settings);
  }

  /** instantiate the central SMTInterpol script from where all others are copied. */
  private static Script getSmtInterpolScript(
      ShutdownNotifier pShutdownNotifier,
      @javax.annotation.Nullable PathCounterTemplate smtLogfile,
      SmtInterpolSettings settings,
      LogManager logger)
      throws InvalidConfigurationException {
    LogProxyForwarder smtInterpolLogProxy =
        new LogProxyForwarder(logger.withComponentName("SMTInterpol"));
    final SMTInterpol smtInterpol =
        new SMTInterpol(smtInterpolLogProxy, pShutdownNotifier::shouldShutdown);

    final Script script = wrapInLoggingScriptIfNeeded(smtInterpol, smtLogfile);

    for (Map.Entry<String, Object> entry : settings.optionsMap.entrySet()) {
      try {
        script.setOption(entry.getKey(), entry.getValue());
      } catch (SMTLIBException | UnsupportedOperationException e) {
        throw new InvalidConfigurationException(
            "Invalid option \"" + entry.getKey() + "=" + entry.getValue() + "\" for SMTInterpol.",
            e);
      }
    }
    // TODO: We would like to use Logics.ALL here and let the solver decide which logics are needed.
    // But ... SMTInterpol eagerly checks logics for model generation,
    // so we limit the available theories here to a large set of logics,
    // including Arrays, UFs, and non-linear arithmetics over Ints and Rationals.
    script.setLogic(Logics.AUFNIRA);
    return script;
  }

  private static Script wrapInLoggingScriptIfNeeded(
      SMTInterpol smtInterpol, @Nullable PathCounterTemplate smtLogfileTemplate)
      throws InvalidConfigurationException {
    if (smtLogfileTemplate == null) {
      return smtInterpol;
    } else {
      Path smtLogfile = smtLogfileTemplate.getFreshPath();
      String filename = smtLogfile.toAbsolutePath().toString();
      try {
        // create a thin wrapper around Benchmark,
        // this allows to write most formulas of the solver to outputfile
        return new LoggingScript(smtInterpol, filename, true, true);
      } catch (IOException e) {
        throw new InvalidConfigurationException(
            "Could not open log file for SMTInterpol queries.", e);
      }
    }
  }

  /**
   * use the copy-constructor of SMTInterpol and create a new script. The new script has its own
   * assertion stack, but shares all symbols.
   */
  private Script createNewScript(Set<ProverOptions> pOptions) {
    Map<String, Object> newOptions = new LinkedHashMap<>(settings.optionsMap);

    // We need to enable interpolation support globally. See above.
    // newOptions.put(":produce-interpolants", enableInterpolation);

    newOptions.put(
        ":produce-unsat-cores",
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)
            || pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS));
    newOptions.put(":produce-models", pOptions.contains(ProverOptions.GENERATE_MODELS));

    SMTInterpol smtInterpol =
        new SMTInterpol(getSmtInterpol(), newOptions, CopyMode.RESET_TO_DEFAULT);
    try {
      return wrapInLoggingScriptIfNeeded(smtInterpol, settings.smtLogfile);
    } catch (InvalidConfigurationException e) {
      throw new IllegalStateException(e);
    }
  }

  /** extract the central SMTInterpol instance. */
  private SMTInterpol getSmtInterpol() {
    final Script script = manager.getEnvironment();
    if (script instanceof SMTInterpol) {
      return (SMTInterpol) script;
    } else if (script instanceof WrapperScript) {
      return checkNotNull((WrapperScript) script).findBacking(SMTInterpol.class);
    } else {
      throw new AssertionError("unexpected class for SMTInterpol: " + script.getClass());
    }
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    Script newScript = createNewScript(options);
    return new SmtInterpolTheoremProver(manager, newScript, options, shutdownNotifier);
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {

    Script newScript = createNewScript(options);
    final SmtInterpolInterpolatingProver prover;
    if (settings.smtLogfile == null) {
      prover = new SmtInterpolInterpolatingProver(manager, newScript, options, shutdownNotifier);
    } else {
      prover =
          new LoggingSmtInterpolInterpolatingProver(
              manager,
              newScript,
              options,
              shutdownNotifier,
              settings.optionsMap,
              settings.smtLogfile.getFreshPath());
    }

    return new IndependentInterpolatingProverEnvironment<>(this, prover.creator, prover, options);
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    throw new UnsupportedOperationException("SMTInterpol does not support optimization");
  }

  @Override
  public String getVersion() {
    QuotedObject program = (QuotedObject) manager.getEnvironment().getInfo(":name");
    QuotedObject version = (QuotedObject) manager.getEnvironment().getInfo(":version");
    return program.getValue() + " " + version.getValue();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.SMTINTERPOL;
  }

  @Override // TODO remove?
  public ImmutableMap<String, String> getStatistics() {
    ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
    flatten(builder, "", manager.getEnvironment().getInfo(":all-statistics"));
    return builder.buildOrThrow();
  }

  /**
   * This method returns a flattened mapping converted from a nested array-based structure, in which
   * each entry is a key-value-pair. The key of such a key-value-pair is a String, the value can be
   * a numeric value or a String.
   *
   * <p>We assume only a small nesting level and only a few keys, otherwise we must improve
   * performance of this method.
   *
   * <p>Example:
   * <li>input: {[a, {[b, 1], [c, 2]}], [d, 3], [e, {[f, 4]}]}
   * <li>output: {ab:1, ac:2, d:3, ef:4}
   */
  static void flatten(ImmutableMap.Builder<String, String> builder, String prefix, Object obj) {
    if (obj instanceof Object[]) { // very type-safe structure! :-(
      if (!prefix.isEmpty()) {
        prefix += ">"; // separator for next nesting level
      }
      for (Object entry : (Object[]) obj) {
        checkArgument(
            entry instanceof Object[],
            "expected key-value-pair, but found an unexpected structure: %s",
            obj);
        Object[] keyValue = (Object[]) entry;
        checkArgument(
            keyValue.length == 2,
            "expected key-value-pair, but found an unexpected structure: %s",
            lazyDeepToString(keyValue));
        flatten(builder, prefix + keyValue[0], keyValue[1]);
      }
    } else {
      builder.put(prefix, obj.toString());
    }
  }

  private static Object lazyDeepToString(Object[] value) {
    return new Object() {
      @Override
      public String toString() {
        return Arrays.deepToString(value);
      }
    };
  }

  @Override
  public void close() {}

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
