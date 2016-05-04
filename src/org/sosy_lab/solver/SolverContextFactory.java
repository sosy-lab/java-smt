/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableSet;

import org.sosy_lab.common.ChildFirstPatternClassLoader;
import org.sosy_lab.common.Classes;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.NullLogManager;
import org.sosy_lab.solver.api.SolverContext;
import org.sosy_lab.solver.logging.LoggingSolverContext;
import org.sosy_lab.solver.mathsat5.Mathsat5SolverContext;
import org.sosy_lab.solver.princess.PrincessSolverContext;

import java.io.File;
import java.lang.ref.WeakReference;
import java.lang.reflect.Constructor;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.logging.Level;
import java.util.regex.Pattern;

import javax.annotation.Nullable;

/**
 * Factory class for loading and generating solver contexts.
 * Generates a {@link SolverContext} corresponding to the chosen
 * solver.
 *
 * <p>Main entry point for JavaSMT.
 */
@Options(prefix = "solver", deprecatedPrefix = "cpa.predicate")
public class SolverContextFactory {

  @VisibleForTesting
  public enum Solvers {
    MATHSAT5,
    SMTINTERPOL,
    Z3,
    Z3JAVA,
    PRINCESS
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

  @Option(secure = true, name = "useLogger", description = "Log solver actions, this may be slow!")
  private boolean useLogger = false;

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final Configuration config;

  public SolverContextFactory(
      Configuration pConfig, LogManager pLogger, ShutdownNotifier pShutdownNotifier)
      throws InvalidConfigurationException {
    pConfig.inject(this);
    logger = checkNotNull(pLogger);
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

        // Loading SmtInterpol is difficult as it requires its own class
        // loader for fiddling with Java_CUP versions.
        return getFactoryForSolver(createSmtInterpolClassLoader(logger), SMTINTERPOL_FACTORY_CLASS)
            .create(config, logger, shutdownNotifier, logfile, randomSeed);

      case MATHSAT5:
        return Mathsat5SolverContext.create(logger, config, shutdownNotifier, logfile, randomSeed);

        // Z3 and Z3Java also require their own custom class loader to perform trickery with the
        // java.library.path without affecting the main class loader.
      case Z3:
        return getFactoryForSolver(z3ClassLoader, Z3_FACTORY_CLASS)
            .create(config, logger, shutdownNotifier, logfile, randomSeed);
      case Z3JAVA:
        return getFactoryForSolver(z3ClassLoader, Z3JAVA_FACTORY_CLASS)
            .create(config, logger, shutdownNotifier, logfile, randomSeed);

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
            NullLogManager.getInstance(),
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
  public static abstract class InnerUtilFactory {

    public SolverContext create(
        Configuration config,
        LogManager logger,
        ShutdownNotifier pShutdownNotifier,
        @Nullable PathCounterTemplate solverLogfile,
        long randomSeed)
        throws InvalidConfigurationException {
      final Thread currentThread = Thread.currentThread();
      final ClassLoader contextClassLoader = currentThread.getContextClassLoader();
      try {
        currentThread.setContextClassLoader(this.getClass().getClassLoader());
        return generateSolverContext(config, logger, pShutdownNotifier, solverLogfile, randomSeed);
      } finally {
        currentThread.setContextClassLoader(contextClassLoader);
      }
    }

    protected abstract SolverContext generateSolverContext(
        Configuration config,
        LogManager logger,
        ShutdownNotifier pShutdownNotifier,
        @Nullable PathCounterTemplate solverLogfile,
        long randomSeed)
        throws InvalidConfigurationException;
  }

  // ---- Custom class loaders ----

  // For SmtInterpol we need a separate class loader
  // because it needs it's own (modified) version of the Java CUP runtime
  // and we might already have the normal (unmodified) version of Java CUP
  // on the class path of the normal class loader.
  private static final String solverPathPrefix = "org.sosy_lab.solver";
  private static final Pattern SMTINTERPOL_CLASSES =
      Pattern.compile(
          "^("
              + Pattern.quote(solverPathPrefix)
              + "\\.smtinterpol|"
              + "de\\.uni_freiburg\\.informatik\\.ultimate|"
              + "java_cup\\.runtime|"
              + "org\\.apache\\.log4j"
              + ")\\..*");
  private static final String SMTINTERPOL_CLASS =
      "de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol";
  private static final String SMTINTERPOL_FACTORY_CLASS =
      solverPathPrefix + ".smtinterpol.SmtInterpolSolverFactory";

  // For Z3 we need a custom class loader as it's JAR file calls "System.loadLibrary",
  // and we have to force it to look in the correct directory.
  private static final String Z3JAVA_FACTORY_CLASS =
      solverPathPrefix + ".z3java.Z3JavaLoadingFactory";
  private static final String Z3_FACTORY_CLASS = solverPathPrefix + ".z3.Z3LoadingFactory";
  private static final Pattern Z3_CLASSES =
      Pattern.compile(
          "^("
              + "com\\.microsoft\\.z3|"
              + Pattern.quote(solverPathPrefix)
              + "\\.z3java|"
              + Pattern.quote(solverPathPrefix)
              + "\\.z3"
              + ")\\..*");

  // Libraries for which we have to supply a custom path.
  private static final Set<String> expectedLibrariesToLoad =
      ImmutableSet.of("libz3java", "libz3j", "z3j", "z3java");

  // Both Z3 and Z3Java have to be loaded using same, custom, class loader.
  private static final ClassLoader z3ClassLoader = createZ3ClassLoader();

  // We keep the class loader for SmtInterpol around
  // in case someone creates a second instance of FormulaManagerFactory
  private static WeakReference<ClassLoader> smtInterpolClassLoader = new WeakReference<>(null);
  private static final AtomicInteger smtInterpolLoadingCount = new AtomicInteger(0);

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

    URL[] urls;
    if (parentClassLoader instanceof URLClassLoader) {
      @SuppressWarnings("resource")
      URLClassLoader uParentClassLoader = (URLClassLoader) parentClassLoader;
      urls = uParentClassLoader.getURLs();
    } else {
      urls =
          new URL[] {
            SolverContextFactory.class.getProtectionDomain().getCodeSource().getLocation(),
          };
    }
    return new CustomLibraryPathClassLoader(Z3_CLASSES, urls, parentClassLoader);
  }

  private static ClassLoader createSmtInterpolClassLoader(LogManager logger) {
    // Cache SMTInterpol class loader using weak reference.
    ClassLoader classLoader = smtInterpolClassLoader.get();
    if (classLoader != null) {
      return classLoader;
    }

    // Garbage collected on first entry.
    if (smtInterpolLoadingCount.incrementAndGet() > 1) {
      logger.log(Level.INFO, "Repeated loading of SmtInterpol");
    }

    classLoader = SolverContextFactory.class.getClassLoader();

    // If possible, create class loader with special class path with only SMTInterpol and JavaSMT.
    // SMTInterpol needs to have its own version of java-cup,
    // so the class loader should not load java-cup classes from any other place.
    String classFile = SMTINTERPOL_CLASS.replace('.', File.separatorChar) + ".class";
    URL url = classLoader.getResource(classFile);
    if (url != null && url.getProtocol().equals("jar") && url.getFile().contains("!")) {
      try {
        url = new URL(url.getFile().substring(0, url.getFile().lastIndexOf('!')));

        URL[] urls = {
          url, SolverContextFactory.class.getProtectionDomain().getCodeSource().getLocation(),
        };

        // By using ChildFirstPatternClassLoader we ensure that classes
        // do not get loaded by the parent class loader.
        classLoader = new ChildFirstPatternClassLoader(SMTINTERPOL_CLASSES, urls, classLoader);

      } catch (MalformedURLException e) {
        logger.logUserException(
            Level.WARNING,
            e,
            "Could not create proper classpath for SMTInterpol, "
                + "loading correct java-cup classes may fail.");
      }
    } else {
      logger.log(
          Level.WARNING,
          "Could not create proper classpath for SMTInterpol because location of SMTInterpol "
              + "classes is unexpected, loading correct java-cup classes may fail. "
              + "Location of SMTInterpol is ",
          url);
    }
    smtInterpolClassLoader = new WeakReference<>(classLoader);
    return classLoader;
  }

  private static class CustomLibraryPathClassLoader extends ChildFirstPatternClassLoader {

    /**
     * Create a new class loader.
     *
     * @param pClassPattern The pattern telling which classes should never be loaded by the parent.
     * @param pUrls         The sources where this class loader should load classes from.
     * @param pParent       The parent class loader.
     */
    CustomLibraryPathClassLoader(Pattern pClassPattern, URL[] pUrls, ClassLoader pParent) {
      super(pClassPattern, pUrls, pParent);
    }

    @Override
    protected String findLibrary(String libname) {
      if (expectedLibrariesToLoad.contains(libname)) {
        String mappedName = System.mapLibraryName(libname);

        // Use the directory-specific folder.
        Path outFile = NativeLibraries.getNativeLibraryPath().resolve(mappedName);
        if (!outFile.exists()) {

          // If fails, use the same directory as the JAR.
          outFile = NativeLibraries.getPathToJar().resolve(mappedName);
        }
        if (!outFile.exists()) {

          // If that fails as well, use standard loading.
          return super.findLibrary(libname);
        }
        return outFile.toAbsolutePath().toString();
      }
      return super.findLibrary(libname);
    }
  }
}
