/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableSet;

import org.sosy_lab.common.Classes;
import org.sosy_lab.common.Classes.ClassLoaderBuilder;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.logging.LoggingSolverContext;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5SolverContext;
import org.sosy_lab.java_smt.solvers.princess.PrincessSolverContext;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolSolverContext;

import java.lang.reflect.Constructor;
import java.net.URLClassLoader;
import java.util.Set;
import java.util.regex.Pattern;

import javax.annotation.Nullable;

/**
 * Factory class for loading and generating solver contexts.
 * Generates a {@link SolverContext} corresponding to the chosen
 * solver.
 *
 * <p>Main entry point for JavaSMT.
 */
@Options(prefix = "solver")
public class SolverContextFactory {

  public enum Solvers {
    MATHSAT5,
    SMTINTERPOL,
    Z3,
    PRINCESS,
    CVC4
  }

  @Option(secure = true, description = "Export solver queries in SmtLib format into a file.")
  private boolean logAllQueries = false;

  @Option(secure = true, description = "Export solver queries in SmtLib format into a file.")
  @FileOption(Type.OUTPUT_FILE)
  private @Nullable PathCounterTemplate logfile =
      PathCounterTemplate.ofFormatString("smtquery.%03d.smt2");

  @Option(secure = true, description = "Random seed for SMT solver.")
  private long randomSeed = 42;

  @Option(secure = true, description = "Which SMT solver to use.")
  private Solvers solver = Solvers.SMTINTERPOL;

  @Option(secure = true, description = "Log solver actions, this may be slow!")
  private boolean useLogger = false;

  @Option(secure = true, description = "Default rounding mode for floating point operations.")
  private FloatingPointRoundingMode floatingPointRoundingMode =
      FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final Configuration config;

  public SolverContextFactory(
      Configuration pConfig, LogManager pLogger, ShutdownNotifier pShutdownNotifier)
      throws InvalidConfigurationException {
    pConfig.inject(this);
    logger = pLogger.withComponentName("JavaSMT");
    shutdownNotifier = checkNotNull(pShutdownNotifier);
    config = pConfig;

    if (!logAllQueries) {
      logfile = null;
    }
  }

  /**
   * Create new context with solver chosen according to the supplied configuration.
   */
  public SolverContext generateContext() throws InvalidConfigurationException {
    return generateContext(solver);
  }

  /**
   * Create new context with solver name supplied.
   */
  @SuppressWarnings("resource") // returns unclosed context object
  public SolverContext generateContext(Solvers solverToCreate)
      throws InvalidConfigurationException {
    SolverContext context;
    try {
      context = generateContext0(solverToCreate);
    } catch (UnsatisfiedLinkError e) {
      throw new InvalidConfigurationException(
          String.format(
              "The SMT solver %s is not available on this machine because of missing libraries "
                  + "(%s). "
                  + "You may experiment with SMTInterpol by setting solver.solver=SMTInterpol.",
              solverToCreate,
              e.getMessage()),
          e);
    }

    if (useLogger) {
      context = new LoggingSolverContext(logger, context);
    }
    return context;
  }

  private SolverContext generateContext0(Solvers solverToCreate)
      throws InvalidConfigurationException {
    switch (solverToCreate) {
      case SMTINTERPOL:
        return SmtInterpolSolverContext.create(
            config, logger, shutdownNotifier, logfile, randomSeed);

      case MATHSAT5:
        return Mathsat5SolverContext.create(
            logger, config, shutdownNotifier, logfile, randomSeed, floatingPointRoundingMode);

      case Z3:

        // Z3 requires its own custom class loader to perform trickery with the
        // java.library.path without affecting the main class loader.
        return getFactoryForSolver(z3ClassLoader, Z3_FACTORY_CLASS)
            .generateSolverContext(
                config, logger, shutdownNotifier, logfile, randomSeed, floatingPointRoundingMode);

      case PRINCESS:
        // TODO: pass randomSeed to Princess
        return PrincessSolverContext.create(config, shutdownNotifier, logfile);

      default:
        throw new AssertionError("no solver selected");
    }
  }

  /**
   * Shortcut for getting a {@link SolverContext},
   * the solver is selected using the configuration {@code config}
   *
   * <p>See
   * {@link #SolverContextFactory(Configuration, LogManager, ShutdownNotifier)}
   * for documentation of accepted parameters.
   */
  public static SolverContext createSolverContext(
      Configuration config, LogManager logger, ShutdownNotifier shutdownNotifier)
      throws InvalidConfigurationException {
    return new SolverContextFactory(config, logger, shutdownNotifier).generateContext();
  }

  /**
   * Shortcut for getting a {@link SolverContext}, the solver is selected using
   * an argument.
   *
   * <p>See
   * {@link #SolverContextFactory(Configuration, LogManager, ShutdownNotifier)}
   * for documentation of accepted parameters.
   */
  public static SolverContext createSolverContext(
      Configuration config, LogManager logger, ShutdownNotifier shutdownNotifier, Solvers solver)
      throws InvalidConfigurationException {
    return new SolverContextFactory(config, logger, shutdownNotifier).generateContext(solver);
  }

  /**
   * Minimalistic shortcut for creating a solver context.
   * Empty default configuration, no logging, and no shutdown notifier.
   *
   * @param solver Solver to initialize
   */
  public static SolverContext createSolverContext(Solvers solver)
      throws InvalidConfigurationException {
    return new SolverContextFactory(
            Configuration.defaultConfiguration(),
            LogManager.createNullLogManager(),
            ShutdownNotifier.createDummy())
        .generateContext(solver);
  }

  /**
   * Interface for completely encapsulating all accesses to a solver's package
   * to decouple the solver's package from the rest of the code.
   *
   * <p>This interface is only meant to be implemented by SMT solvers
   * and used by this class, not by other classes.
   */
  public abstract static class InnerUtilFactory {

    protected abstract SolverContext generateSolverContext(
        Configuration config,
        LogManager logger,
        ShutdownNotifier pShutdownNotifier,
        @Nullable PathCounterTemplate solverLogfile,
        long randomSeed,
        FloatingPointRoundingMode pFloatingPointRoundingMode)
        throws InvalidConfigurationException;
  }

  // ---- Custom class loaders ----

  // For Z3 we need a custom class loader as it's JAR file calls "System.loadLibrary",
  // and we have to force it to look in the correct directory.
  private static final String Z3_PACKAGE = "org.sosy_lab.java_smt.solvers.z3";
  private static final String Z3_FACTORY_CLASS = Z3_PACKAGE + ".Z3LoadingFactory";
  private static final Pattern Z3_CLASSES =
      Pattern.compile("^(" + "com\\.microsoft\\.z3|" + Pattern.quote(Z3_PACKAGE) + ")\\..*");

  // Libraries for which we have to supply a custom path.
  private static final Set<String> Z3_LIBRARY_NAMES =
      ImmutableSet.of("z3", "libz3", "libz3java", "z3java");

  // Both Z3 and Z3Java have to be loaded using same, custom, class loader.
  private static final ClassLoader z3ClassLoader = createZ3ClassLoader();

  private InnerUtilFactory getFactoryForSolver(ClassLoader pClassLoader, String factoryClassName) {
    try {
      @SuppressWarnings("unchecked")
      Class<? extends InnerUtilFactory> factoryClass =
          (Class<? extends InnerUtilFactory>) pClassLoader.loadClass(factoryClassName);
      Constructor<? extends InnerUtilFactory> factoryConstructor = factoryClass.getConstructor();
      return factoryConstructor.newInstance();
    } catch (ReflectiveOperationException e) {
      throw new Classes.UnexpectedCheckedException("Failed to load" + factoryClassName, e);
    }
  }

  private static ClassLoader createZ3ClassLoader() {
    ClassLoader parentClassLoader = SolverContextFactory.class.getClassLoader();

    ClassLoaderBuilder builder =
        Classes.makeExtendedURLClassLoader()
            .setParent(parentClassLoader)
            .setDirectLoadClasses(Z3_CLASSES)
            .setCustomLookupNativeLibraries(Z3_LIBRARY_NAMES::contains);

    if (parentClassLoader instanceof URLClassLoader) {
      @SuppressWarnings("resource")
      URLClassLoader uParentClassLoader = (URLClassLoader) parentClassLoader;
      builder.setUrls(uParentClassLoader.getURLs());
    } else {
      builder.setUrls(
          SolverContextFactory.class.getProtectionDomain().getCodeSource().getLocation());
    }

    return builder.build();
  }
}
