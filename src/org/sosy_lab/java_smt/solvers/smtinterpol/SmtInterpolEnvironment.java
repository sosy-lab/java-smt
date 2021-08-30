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
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringReader;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.nio.charset.Charset;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.IO;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This is a Wrapper around SmtInterpol. It guarantees the stack-behavior of function-declarations
 * towards the SmtSolver, so functions remain declared, if levels are popped. This Wrapper allows to
 * set a logfile for all Smt-Queries (default "smtinterpol.smt2").
 */
@Options(prefix = "solver.smtinterpol")
public class SmtInterpolEnvironment {

  /** SMTInterpol does not allow to use key-functions as identifiers. */
  private static final ImmutableSet<String> UNSUPPORTED_IDENTIFIERS =
      ImmutableSet.of("true", "false", "select", "store", "or", "and", "xor", "distinct");

  @Option(
      secure = true,
      description =
          "Double check generated results like interpolants and models whether they are correct")
  private boolean checkResults = false;

  private final @Nullable PathCounterTemplate smtLogfile;

  @Option(
      secure = true,
      description =
          "Further options that will be set to true for SMTInterpol "
              + "in addition to the default options. Format is 'option1,option2,option3'")
  private List<String> furtherOptions = ImmutableList.of();

  private final LogManager logger;
  private final LogProxy smtInterpolLogProxy;
  private final ShutdownNotifier shutdownNotifier;

  /** the wrapped Script. */
  private final Script script;

  private final Theory theory;

  /** The current depth of the stack in the solver. */
  private int stackDepth = 0;

  /** The Constructor creates the wrapped Element, sets some options and initializes the logger. */
  SmtInterpolEnvironment(
      Configuration config,
      final LogManager pLogger,
      final ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pSmtLogfile,
      long randomSeed)
      throws InvalidConfigurationException {
    config.inject(this);
    logger = pLogger;
    shutdownNotifier = checkNotNull(pShutdownNotifier);
    smtLogfile = pSmtLogfile;
    smtInterpolLogProxy = new LogProxyForwarder(logger.withComponentName("SMTInterpol"));

    final SMTInterpol smtInterpol =
        new SMTInterpol(smtInterpolLogProxy, pShutdownNotifier::shouldShutdown);

    if (smtLogfile != null) {
      script = createLoggingWrapper(smtInterpol);
    } else {
      script = smtInterpol;
    }

    script.setOption(":global-declarations", true);
    script.setOption(":random-seed", randomSeed);
    script.setOption(":produce-interpolants", true);
    script.setOption(":produce-models", true);
    script.setOption(":produce-unsat-cores", true);
    if (checkResults) {
      script.setOption(":interpolant-check-mode", true);
      script.setOption(":unsat-core-check-mode", true);
      script.setOption(":model-check-mode", true);
    }
    // TODO: We would like to use Logics.ALL here and let the solver decide which logics are needed.
    // But ... SMTInterpol eagerly checks logics for model generation,
    // so we limit the available theories here to a large set of logics,
    // including Arrays, UFs, and non-linear arithmetics over Ints and Rationals.
    script.setLogic(Logics.AUFNIRA);

    for (String option : furtherOptions) {
      try {
        script.setOption(":" + option, true);
      } catch (SMTLIBException | UnsupportedOperationException e) {
        throw new InvalidConfigurationException(
            "Invalid option \"" + option + "\" for SMTInterpol.", e);
      }
    }

    theory = smtInterpol.getTheory();
  }

  private Script createLoggingWrapper(SMTInterpol smtInterpol) {
    assert smtLogfile != null;
    String filename = smtLogfile.getFreshPath().toAbsolutePath().toString();
    try {
      // create a thin wrapper around Benchmark,
      // this allows to write most formulas of the solver to outputfile
      return new LoggingScript(smtInterpol, filename, true, true);
    } catch (IOException e) {
      logger.logUserException(Level.WARNING, e, "Could not open log file for SMTInterpol queries");
      // go on without logging
      return smtInterpol;
    }
  }

  /**
   * Be careful when accessing the Theory directly, because operations on it won't be caught by the
   * LoggingScript. It is ok to create terms using the Theory, not to define them or call checkSat.
   */
  Theory getTheory() {
    return theory;
  }

  SmtInterpolInterpolatingProver getInterpolator(
      SmtInterpolFormulaManager mgr, Set<ProverOptions> pOptions) {
    if (smtLogfile != null) {
      Path logfile = smtLogfile.getFreshPath();

      try {
        @SuppressWarnings("IllegalInstantiation")
        PrintWriter out = new PrintWriter(IO.openOutputFile(logfile, Charset.defaultCharset()));

        out.println("(set-option :global-declarations true)");
        out.println("(set-option :random-seed " + script.getOption(":random-seed") + ")");
        out.println("(set-option :produce-interpolants true)");
        out.println(
            String.format(
                "(set-option :produce-models %s)",
                pOptions.contains(ProverOptions.GENERATE_MODELS)));
        out.println(
            String.format(
                "(set-option :produce-unsat-cores %s)",
                pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)));
        if (checkResults) {
          out.println("(set-option :interpolant-check-mode true)");
          out.println("(set-option :unsat-core-check-mode true)");
          out.println("(set-option :model-check-mode true)");
        }

        out.println("(set-logic " + theory.getLogic().name() + ")");
        return new LoggingSmtInterpolInterpolatingProver(mgr, pOptions, out);
      } catch (IOException e) {
        logger.logUserException(Level.WARNING, e, "Could not write interpolation query to file");
      }
    }

    return new SmtInterpolInterpolatingProver(mgr, pOptions);
  }

  int getStackDepth() {
    return stackDepth;
  }

  /**
   * Parse a String to Terms and Declarations. The String may contain terms and
   * function-declarations in SMTLIB2-format. Use Prefix-notation!
   */
  public List<Term> parseStringToTerms(String s) {
    FormulaCollectionScript parseScript = new FormulaCollectionScript(script, theory);
    ParseEnvironment parseEnv =
        new ParseEnvironment(parseScript, new OptionMap(smtInterpolLogProxy, true)) {
          @Override
          public void printError(String pMessage) {
            throw new SMTLIBException(pMessage);
          }

          @Override
          public void printSuccess() {}
        };

    try {
      parseEnv.parseStream(new StringReader(s), "<stdin>");
    } catch (SMTLIBException nested) {
      throw new IllegalArgumentException(nested);
    }

    return parseScript.getAssertedTerms();
  }

  public void setOption(String opt, Object value) {
    script.setOption(opt, value);
  }

  /**
   * This function declares a new functionSymbol, that has a given (result-) sort. The params for
   * the functionSymbol also have sorts. If you want to declare a new variable, i.e. "X", paramSorts
   * is an empty array.
   */
  @CanIgnoreReturnValue
  public FunctionSymbol declareFun(String fun, Sort[] paramSorts, Sort resultSort) {
    checkSymbol(fun);
    FunctionSymbol fsym = theory.getFunction(fun, paramSorts);

    if (fsym == null) {
      script.declareFun(fun, paramSorts, resultSort);
      return theory.getFunction(fun, paramSorts);
    } else {
      if (!fsym.getReturnSort().equals(resultSort)) {
        throw new IllegalArgumentException(
            "Function " + fun + " is already declared with different definition");
      }
      if (fun.equals("true") || fun.equals("false")) {
        throw new IllegalArgumentException("Cannot declare a variable named " + fun);
      }
      return fsym;
    }
  }

  public void push(int levels) {
    checkArgument(levels > 0);
    script.push(levels);
    stackDepth += levels;
  }

  /**
   * This function pops levels from the assertion-stack. It also declares popped functions on the
   * lower level.
   */
  public void pop(int levels) {
    checkArgument(levels >= 0);
    checkState(stackDepth >= levels, "not enough levels to remove");
    script.pop(levels);
    stackDepth -= levels;
  }

  /** This function adds the term on top of the stack. */
  public void assertTerm(Term term) {
    checkState(
        stackDepth > 0,
        "assertions should be on higher levels, "
            + "because we might need to remove the term again and "
            + "we have a shared environment for all provers.");
    script.assertTerm(term);
  }

  /**
   * This function causes the SatSolver to check all the terms on the stack, if their conjunction is
   * SAT or UNSAT.
   */
  public boolean checkSat() throws InterruptedException {
    // We actually terminate SmtInterpol during the analysis
    // by using a shutdown listener. However, SmtInterpol resets the
    // mStopEngine flag in DPLLEngine before starting to solve,
    // so we check here, too.
    shutdownNotifier.shutdownIfNecessary();

    LBool result = script.checkSat();
    switch (result) {
      case SAT:
        return true;
      case UNSAT:
        return false;
      case UNKNOWN:
        Object reason = script.getInfo(":reason-unknown");
        if (!(reason instanceof ReasonUnknown)) {
          throw new SMTLIBException("checkSat returned UNKNOWN with unknown reason " + reason);
        }
        switch ((ReasonUnknown) reason) {
          case MEMOUT:
            // SMTInterpol catches OOM, but we want to have it thrown.
            throw new OutOfMemoryError("Out of memory during SMTInterpol operation");
          case CANCELLED:
            shutdownNotifier.shutdownIfNecessary(); // expected if we requested termination
            throw new SMTLIBException("checkSat returned UNKNOWN with unexpected reason " + reason);
          default:
            throw new SMTLIBException("checkSat returned UNKNOWN with unexpected reason " + reason);
        }

      default:
        throw new SMTLIBException("checkSat returned " + result);
    }
  }

  public Iterable<Term[]> checkAllSat(Term[] importantPredicates) throws InterruptedException {
    // We actually terminate SmtInterpol during the analysis
    // by using a shutdown listener. However, SmtInterpol resets the
    // mStopEngine flag in DPLLEngine before starting to solve,
    // so we check here, too.
    shutdownNotifier.shutdownIfNecessary();

    return script.checkAllsat(importantPredicates);
  }

  /** This function returns a map, that contains assignments for all terms. */
  public Model getModel() {
    try {
      return script.getModel();
    } catch (SMTLIBException e) {
      if (e.getMessage().contains("Context is inconsistent")) {
        throw new IllegalStateException(BasicProverEnvironment.NO_MODEL_HELP, e);
      } else {
        // new stacktrace, but only the library calls are missing.
        throw e;
      }
    }
  }

  public Object getInfo(String info) {
    return script.getInfo(info);
  }

  public Sort getBooleanSort() {
    return theory.getBooleanSort();
  }

  public Sort getIntegerSort() {
    return theory.getNumericSort();
  }

  public Sort getRealSort() {
    return theory.getRealSort();
  }

  /** This function returns an n-ary sort with given parameters. */
  Sort sort(String sortname, Sort... params) {
    return script.sort(sortname, params);
  }

  public Term term(String funcname, Term... params) {
    return script.term(funcname, params);
  }

  public Term term(String funcname, String[] indices, @Nullable Sort returnSort, Term... params) {
    return script.term(funcname, indices, returnSort, params);
  }

  public TermVariable variable(String varname, Sort sort) {
    checkSymbol(varname);
    return script.variable(varname, sort);
  }

  public Term quantifier(int quantor, TermVariable[] vars, Term body, Term[]... patterns) {
    return script.quantifier(quantor, vars, body, patterns);
  }

  public Term let(TermVariable[] pVars, Term[] pValues, Term pBody) {
    return script.let(pVars, pValues, pBody);
  }

  public Term annotate(Term t, Annotation... annotations) {
    return script.annotate(t, annotations);
  }

  /** returns a number of type INT or REAL. */
  public Term numeral(BigInteger num) {
    return script.numeral(num);
  }

  /** returns a number of type INT or REAL. */
  public Term numeral(String num) {
    return script.numeral(num);
  }

  /** returns a number of type REAL. */
  public Term decimal(String num) {
    return script.decimal(num);
  }

  /** returns a number of type REAL. */
  public Term decimal(BigDecimal num) {
    return script.decimal(num);
  }

  public Term hexadecimal(String hex) {
    return script.hexadecimal(hex);
  }

  public Term binary(String bin) {
    return script.binary(bin);
  }

  /**
   * Compute a sequence of interpolants. The nesting array describes the start of the subtree for
   * tree interpolants. For inductive sequences of interpolants use a nesting array completely
   * filled with 0.
   *
   * <p>Example:
   *
   * <pre>
   * A  D
   * |  |
   * B  E
   * | /
   * C
   * |
   * F  H
   * | /
   * G
   *
   * arrayIndex     = [0,1,2,3,4,5,6,7]  // only for demonstration, not needed
   * partition      = [A,B,D,E,C,F,H,G]  // post-order of tree
   * startOfSubTree = [0,0,2,2,0,0,6,0]  // index of left-most leaf of the current element
   * </pre>
   *
   * @param partition The array of formulas (post-order of tree). This should contain either
   *     top-level names or conjunction of top-level names.
   * @param startOfSubTree The start of the subtree containing the formula at this index as root.
   * @return Tree interpolants respecting the nesting relation.
   */
  public Term[] getTreeInterpolants(Term[] partition, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    checkState(stackDepth > 0, "interpolants should be on higher levels");
    try {
      return script.getInterpolants(partition, startOfSubTree);
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
  }

  public Term[] getUnsatCore() {
    checkState(stackDepth > 0, "unsat core should be on higher levels");
    return script.getUnsatCore();
  }

  public Term simplify(Term input) {
    SimplifyDDA s = new SimplifyDDA(script, true);
    return s.getSimplifiedTerm(input);
  }

  /** This function returns the version of SmtInterpol, for logging. */
  public String getVersion() {
    QuotedObject program = (QuotedObject) script.getInfo(":name");
    QuotedObject version = (QuotedObject) script.getInfo(":version");
    return program.getValue() + " " + version.getValue();
  }

  /**
   * Copied from {@link NoopScript#checkSymbol}.
   *
   * <p>Check that the symbol does not contain characters that would make it impossible to use it in
   * a LoggingScript. These are | and \.
   *
   * @param symbol the symbol to check
   * @throws IllegalArgumentException if symbol contains | or \.
   */
  private void checkSymbol(String symbol) throws SMTLIBException {
    checkArgument(
        symbol.indexOf('|') == -1 && symbol.indexOf('\\') == -1, "Symbol must not contain | or \\");
    checkArgument(
        !UNSUPPORTED_IDENTIFIERS.contains(symbol),
        "SMTInterpol does not support %s as identifier.",
        symbol);
  }
}
