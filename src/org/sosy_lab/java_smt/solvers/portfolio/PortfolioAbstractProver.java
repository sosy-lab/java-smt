/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.util.concurrent.MoreExecutors.listeningDecorator;
import static java.util.concurrent.Executors.newFixedThreadPool;

import com.google.common.base.Preconditions;
import com.google.common.base.Throwables;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Multimap;
import com.google.common.util.concurrent.Futures;
import com.google.common.util.concurrent.ListenableFuture;
import com.google.common.util.concurrent.ListeningExecutorService;
import com.google.common.util.concurrent.ThreadFactoryBuilder;
import com.google.common.util.concurrent.Uninterruptibles;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Classes.UnexpectedCheckedException;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

// TODO: is the statistics wrapper sufficient to get all info about nested solvers?
@SuppressWarnings("unused")
abstract class PortfolioAbstractProver<I, P extends BasicProverEnvironment<?>>
    extends AbstractProver<I> {

  private final PortfolioSolverContext portfolioContext;
  // Before using a prover, we need to make sure not to use provers that have been kicked out
  // Currently we only build provers to be used from the options of this one when actually
  // requesting to solve something, so it's fine for now
  // TODO: for incremental this is not sufficient
  private Map<Solvers, P> centralSolversAndProvers;
  private static final Map<Solvers, AtomicInteger> terminatedFirstCounter =
      new ConcurrentHashMap<>();

  private final Set<ProverOptions> options;

  // We keep the original contexts etc. in the creator
  private final PortfolioFormulaCreator creator;
  private final ShutdownNotifier externalShutdownNotifier;
  private final LogManager logger;
  private final ParallelProverStatistics stats;

  private final boolean immediatelyGetModel = true;

  private List<ValueAssignment> lastModelAssignments;
  // For each renewed run
  private ShutdownManager centralShutdownManager;
  private final AtomicBoolean terminatedCurrentCall = new AtomicBoolean(false);

  private @Nullable ParallelProverResult lastResult;

  protected PortfolioAbstractProver(
      PortfolioSolverContext pPortfolioContext,
      Set<ProverOptions> pOptions,
      Map<Solvers, SolverContext> pSolverContexts,
      PortfolioFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      LogManager pLogger) {
    super(pOptions);
    portfolioContext = pPortfolioContext;
    centralSolversAndProvers =
        generateNewProvers(pSolverContexts, pOptions, pLogger, terminatedFirstCounter);
    options = pOptions;
    externalShutdownNotifier = pShutdownNotifier;
    creator = pCreator;
    logger = pLogger;
    stats = null;
  }

  protected synchronized void handleUnsupportedOperationWithReason(
      Solvers solver, String reason, P threadedProver) {
    threadedProver.close();
    centralSolversAndProvers.get(solver).close();
    ImmutableMap.Builder<Solvers, P> newCentralSolversAndProvers = ImmutableMap.builder();
    for (Entry<Solvers, P> solverAndCentralProver : centralSolversAndProvers.entrySet()) {
      if (solverAndCentralProver.getKey() != solver) {
        newCentralSolversAndProvers.put(solverAndCentralProver);
      }
    }
    centralSolversAndProvers = newCentralSolversAndProvers.buildOrThrow();
    creator.handleUnsupportedOperationWithReason(solver, reason);
  }

  protected Map<Solvers, P> getCentralSolversAndProvers() {
    return centralSolversAndProvers;
  }

  private Map<Solvers, P> generateNewProvers(
      Map<Solvers, SolverContext> pSolverContexts,
      Set<ProverOptions> pOptions,
      LogManager pLogger,
      Map<Solvers, AtomicInteger> terminatedFirstCounter) {
    ImmutableMap.Builder<Solvers, P> builder = ImmutableMap.builder();
    for (Entry<Solvers, SolverContext> e : pSolverContexts.entrySet()) {
      Solvers solver = e.getKey();
      try {
        builder.put(solver, getNewSolverSpecificProver(e.getValue(), pOptions));
        if (!terminatedFirstCounter.containsKey(e.getKey())) {
          terminatedFirstCounter.put(solver, new AtomicInteger(0));
        }
      } catch (UnsupportedOperationException ex) {
        // Log and do nothing. Solver does not support this.
        pLogger.log(
            Level.INFO, "Solver " + solver + " does not support the chosen prover type", ex);
      }
    }
    return builder.buildOrThrow();
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // Start all threads
    centralShutdownManager = ShutdownManager.createWithParent(externalShutdownNotifier);
    ImmutableList.Builder<Callable<ParallelProverResult>> callables = ImmutableList.builder();
    for (Entry<Solvers, P> solverAndMainProver : centralSolversAndProvers.entrySet()) {
      Solvers solver = solverAndMainProver.getKey();
      P mainProver = solverAndMainProver.getValue();
      SolverContext solverContext = creator.getSolverSpecificContexts().get(solver);
      callables.add(createParallelIsUnsat(solver, solverContext, mainProver));
    }
    ParallelProverResult result = buildThreadsAndRunCalls(callables.build());

    if (result.hasValidIsUnsat()) {
      // Cache model if we are SAT
      boolean isUnsat = result.getIsUnsat().orElseThrow();
      if (!isUnsat) {
        lastModelAssignments = result.getModelToList().orElseThrow();
      }
      return isUnsat;
    }

    throw new SolverException("Error: no result for current portfolio of solvers returned");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    // Start all threads
    // TODO:
    throw new UnsupportedOperationException();
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    throw new UnsupportedOperationException("Implement me");
    // return new CachingModel(new PortfolioModel(this));
  }

  @SuppressWarnings("resource")
  @Override
  public Evaluator getEvaluator() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    throw new UnsupportedOperationException("Implement me");
    // return registerEvaluator(new PortfolioEvaluator(this));
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    for (P prover : centralSolversAndProvers.values()) {
      prover.push();
    }
  }

  @Override
  protected void popImpl() {
    closeAllEvaluators();
    for (P prover : centralSolversAndProvers.values()) {
      prover.pop();
    }
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    for (Entry<Solvers, P> solverAndProver : centralSolversAndProvers.entrySet()) {
      Preconditions.checkState(
          solverAndProver.getValue().size() == super.size(),
          "specialized prover %s stack-size %s does not match portfolio-solver stack-size %s",
          solverAndProver.getKey(),
          solverAndProver.getValue().size(),
          super.size());
    }
    return super.size();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    throw new UnsupportedOperationException("Implement me");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Preconditions.checkNotNull(assumptions);
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    throw new UnsupportedOperationException("Implement me");
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    throw new UnsupportedOperationException("Implement me");
  }

  @Override
  public void close() {
    if (!closed) {
      for (P prover : centralSolversAndProvers.values()) {
        prover.close();
      }
    }
    super.close();
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkGenerateAllSat();

    throw new UnsupportedOperationException("Implement me");
  }

  private Callable<ParallelProverResult> createParallelIsUnsat(
      final Solvers solver, final SolverContext contextToBuildFrom, final P proverToBuildFrom) {

    final LogManager singleLogger = logger.withComponentName("Parallel isUnsat() with " + solver);

    // TODO: add option to let solvers run until they finish, or a certain amount of time, or
    //  until they are some time behind the best solver
    // final ResourceLimitChecker singleAnalysisOverallLimit =
    //  ResourceLimitChecker.fromConfiguration(, singleLogger, singleShutdownManager);

    AtomicBoolean terminatedSingleSolver = new AtomicBoolean(false);
    AtomicInteger terminatedCounter = terminatedFirstCounter.get(solver);
    terminatedCurrentCall.set(false);
    // StatisticsEntry statisticsEntry = stats.getNewSubStatistics(solver.toString(), terminated,
    //   terminatedFirstCount);

    return () ->
        runParallelIsUnsat(
            this,
            solver,
            contextToBuildFrom,
            proverToBuildFrom,
            immediatelyGetModel,
            singleLogger,
            terminatedSingleSolver,
            terminatedCounter,
            terminatedCurrentCall);
  }

  // TODO: add update listener that gets new info like getModel/interpolation and allow reuse of
  //  the thread.
  private ParallelProverResult runParallelIsUnsat(
      final PortfolioAbstractProver<I, P> centralPortfolioProver,
      final Solvers usedSolver,
      final SolverContext contextToBuildFrom,
      final P proverToBuildFrom,
      final boolean immediatelyGetModel,
      final LogManager singleLogger,
      //  final ResourceLimitChecker
      //  singleAnalysisOverallLimit,
      final AtomicBoolean terminatedSingleSolver,
      final AtomicInteger terminatedCounter,
      final AtomicBoolean
          terminatedCurrentCall) { // handleFutureResults needs to handle all the exceptions
    // declared here
    try {

      SolverContextAndProverAndShutdownManager newComponents =
          buildNewEmptyContextAndProverFrom(usedSolver, proverToBuildFrom);
      translateSolverStackTo(
          centralPortfolioProver, contextToBuildFrom, proverToBuildFrom, newComponents);

      P prover = newComponents.getProver();
      ShutdownManager shutdownNotifierInThread = newComponents.getShutdownNotifier();

      boolean isUnsat = prover.isUnsat();
      System.out.println(isUnsat);

      List<ValueAssignment> modelAssignments = null;
      if (!isUnsat && immediatelyGetModel) {
        modelAssignments = prover.getModel().asList();
      }
      if (terminatedCurrentCall.get()) {
        System.out.println("Result returned but we already had a result");
      }
      return ParallelProverResult.of(isUnsat, modelAssignments, usedSolver);

    } catch (InterruptedException pE) {
      singleLogger.logUserException(Level.INFO, pE, "Solver " + usedSolver + " was interrupted");
      return ParallelProverResult.absent(usedSolver);

    } catch (SolverException pE) {
      singleLogger.logUserException(
          Level.INFO, pE, "Solver " + usedSolver + " terminated with " + "solver error");
      return ParallelProverResult.absent(usedSolver);

    } finally {
      /*
      try {
        TickerWithUnit threadCpuTime = Tickers.getCurrentThreadCputime();
       pStatisticsEntry.threadCpuTime = TimeSpan.of(threadCpuTime.read(), threadCpuTime.unit());
      } catch (UnsupportedOperationException e) {
        singleLogger.logDebugException(e);
      }
      */
      // Should only be reachable for valid results!
      if (terminatedCurrentCall.compareAndExchange(false, true)) {
        terminatedCounter.getAndIncrement();
      }
      terminatedSingleSolver.set(true);
    }
  }

  public ParallelProverResult buildThreadsAndRunCalls(List<Callable<ParallelProverResult>> calls)
      throws InterruptedException, SolverException {

    ThreadFactory threadFactory =
        new ThreadFactoryBuilder().setNameFormat(getClass().getSimpleName() + "-thread-%d").build();
    ListeningExecutorService exec =
        listeningDecorator(newFixedThreadPool(calls.size(), threadFactory));

    List<ListenableFuture<ParallelProverResult>> futures = new ArrayList<>(calls.size());
    lastResult = null;
    for (Callable<ParallelProverResult> call : calls) {
      futures.add(exec.submit(call));
    }

    // shutdown the executor service,
    exec.shutdown();

    try {
      handleFutureResults(futures);

    } finally {
      // Wait some time so that all threads/solvers have the chance to terminate or shut-down.
      // (necessary for statistics).
      // Time limit here should be somewhat shorter than in ForceTerminationOnShutdown.
      if (!Uninterruptibles.awaitTerminationUninterruptibly(exec, 2, TimeUnit.SECONDS)) {
        logger.log(Level.WARNING, "Not all threads are terminated although we have a result.");
      }

      exec.shutdownNow();
    }

    if (lastResult != null) {
      return lastResult;
    }

    throw new SolverException(
        "Portfolio solver did not recieve a valid result for the current "
            + "query. Please choose a different portfolio or settings.");
  }

  public static class ParallelProverResult {

    private final Solvers solver;
    // Empty for errors
    private final Optional<Boolean> isUnsat;
    // Empty for errors or not requested
    private final Optional<List<ValueAssignment>> maybeModel;

    private ParallelProverResult(
        Optional<Boolean> pIsUnsat, Optional<List<ValueAssignment>> pMaybeModel, Solvers pSolver) {
      solver = pSolver;
      isUnsat = pIsUnsat;
      maybeModel = pMaybeModel;
    }

    public static ParallelProverResult of(
        @Nullable Boolean pIsUnsat, @Nullable List<ValueAssignment> pMaybeModel, Solvers pSolver) {
      return new ParallelProverResult(
          Optional.ofNullable(pIsUnsat), Optional.ofNullable(pMaybeModel), pSolver);
    }

    public static ParallelProverResult of(@Nullable Boolean pIsUnsat, Solvers pSolver) {
      return new ParallelProverResult(Optional.ofNullable(pIsUnsat), Optional.empty(), pSolver);
    }

    public static ParallelProverResult absent(Solvers pSolver) {
      return new ParallelProverResult(Optional.empty(), Optional.empty(), pSolver);
    }

    public boolean hasValidIsUnsat() {
      return isUnsat.isPresent();
    }

    public Optional<List<ValueAssignment>> getModelToList() {
      return maybeModel;
    }

    public Optional<Boolean> getIsUnsat() {
      return isUnsat;
    }

    public Solvers getSolver() {
      return solver;
    }
  }

  private static class StatisticsEntry {

    private final Collection<Statistics> subStatistics;

    private final String name;

    private volatile @Nullable TimeSpan threadCpuTime;

    // Failed to be terminated in the end
    private final AtomicBoolean terminated;

    private final AtomicInteger terminatedFirstCount;

    private StatisticsEntry(
        Collection<Statistics> pSubStatistics,
        String pName,
        AtomicBoolean pTerminated,
        AtomicInteger pTerminatedFirstCount) {
      subStatistics = Objects.requireNonNull(pSubStatistics);
      name = Objects.requireNonNull(pName);
      terminated = Objects.requireNonNull(pTerminated);
      terminatedFirstCount = Objects.requireNonNull(pTerminatedFirstCount);
    }
  }

  private void handleFutureResults(List<ListenableFuture<ParallelProverResult>> futures)
      throws InterruptedException, SolverException {

    // List<Exception> exceptions = new ArrayList<>();
    for (ListenableFuture<ParallelProverResult> f : Futures.inCompletionOrder(futures)) {
      try {
        ParallelProverResult result = f.get();
        if (result.hasValidIsUnsat() && lastResult == null) {
          lastResult = result;

          // cancel other computations
          futures.forEach(future -> future.cancel(true));
          logger.log(Level.INFO, result.getSolver().name() + " finished successfully.");
          // Kill the other provers that are still running
          shutdownRunningProvers("Cancel all remained provers as we have a valid result");
        } else {
          // None returned a valid result?
          throw new SolverException(
              "Portfolio solver has encountered a critical problem when "
                  + "recieving results and can not continue");
        }
      } catch (ExecutionException e) {
        Throwable cause = e.getCause();

        // runParallelAnalysis only declares CPAException, so this is unchecked or unexpected.
        // Cancel other computations and propagate.
        futures.forEach(future -> future.cancel(true));

        shutdownRunningProvers(
            "cancelling all remaining analyses due to critical error when " + "retrieving result");
        Throwables.throwIfUnchecked(cause);
        throw new UnexpectedCheckedException("solver threw: ", cause);

      } catch (CancellationException e) {
        // do nothing, this is normal if we cancel other analyses
      }
    }

    // No result, propagate the found exceptions upwards
    // TODO: ?
  }

  private void shutdownRunningProvers(String reason) {
    // TODO: only kill who's not done.
    centralShutdownManager.requestShutdown(reason);
  }

  // TODO: does this work? We are currently not on the thread of the main context/prover

  /**
   * @param centralPortfolioProver calling/building portfolio prover, so that we can throw out
   *     failing solvers.
   * @param contextToBuildFrom solver specific context
   * @param proverToBuildFrom solver specific prover
   * @param target new solver specific context, prover etc. that is the target of the stack
   *     translation of proverToBuildFrom, so that its stack is 1:1.
   */
  @SuppressWarnings("unchecked")
  protected void translateSolverStackTo(
      PortfolioAbstractProver<I, P> centralPortfolioProver,
      SolverContext contextToBuildFrom,
      P proverToBuildFrom,
      SolverContextAndProverAndShutdownManager target)
      throws InterruptedException {
    FormulaManager originalMgr = contextToBuildFrom.getFormulaManager();
    List<? extends Multimap<BooleanFormula, ?>> currentStack =
        proverToBuildFrom.getInternalAssertedFormulas();

    FormulaManager targetMgr = target.getSolverContext().getFormulaManager();
    P targetProver = target.getProver();

    // Iterates from the lowest level to the highest
    // We assume that interpolation points are consistent
    for (Multimap<BooleanFormula, ?> level : currentStack) {
      // Push
      targetProver.push();
      for (BooleanFormula formula : level.keySet()) {
        // Translate and assert
        try {
          targetProver.addConstraint(targetMgr.translateFrom(formula, originalMgr));
        } catch (UnsupportedOperationException pUnsupportedOperationException) {
          // Solver can't parse or dump, kick out of portfolio
          String reason;
          String failingMethod = pUnsupportedOperationException.getStackTrace()[0].getMethodName();
          if (failingMethod.contains("parseImpl")) {
            reason = "parsing SMTLib2 not supported by the solver or JavaSMT";
          } else if (failingMethod.contains("dumpFormulaImpl")) {
            reason = "dumping SMTLib2 not supported by the solver or JavaSMT";
          } else {
            reason = "Unknown reason";
          }
          centralPortfolioProver.handleUnsupportedOperationWithReason(
              contextToBuildFrom.getSolverName(), reason, targetProver);
        }
      }
    }
  }

  /**
   * Only to be called in the thread this is supposed to execute the solving! Override for
   * specialized Provers! The context/prover returned is empty! You still need to add the stack
   * etc.!
   */
  protected SolverContextAndProverAndShutdownManager buildNewEmptyContextAndProverFrom(
      Solvers solver, P proverToBuildFrom) {
    // If users request shutdown, we want all to shut down
    ShutdownManager shutdownManagerForNew =
        ShutdownManager.createWithParent(centralShutdownManager.getNotifier());
    ShutdownNotifier newNotifier = shutdownManagerForNew.getNotifier();

    SolverContext newEmptyContextWSameOptions =
        portfolioContext.copySolverContextWithNewShutdownNotifier(solver, newNotifier);

    P newProver = getNewSolverSpecificProver(newEmptyContextWSameOptions, options);

    SolverContextAndProverAndShutdownManager triple =
        new SolverContextAndProverAndShutdownManager(
            newEmptyContextWSameOptions, newProver, shutdownManagerForNew);

    return triple;
  }

  /**
   * Only to be called in the thread this is supposed to execute the solving! Override for
   * specialized Provers! The context/prover returned is empty! You still need to add the stack
   * etc.!
   */
  abstract P getNewSolverSpecificProver(
      SolverContext newEmptyContextWSameOptionsForSolver, Set<ProverOptions> pOptions);

  public class SolverContextAndProverAndShutdownManager {

    private final SolverContext solverContext;
    private final P prover;
    private final ShutdownManager shutdownMgr;

    public SolverContextAndProverAndShutdownManager(
        SolverContext ctx, P pProver, ShutdownManager pShutdownMgr) {
      solverContext = checkNotNull(ctx);
      prover = checkNotNull(pProver);
      shutdownMgr = checkNotNull(pShutdownMgr);
    }

    public P getProver() {
      return prover;
    }

    public SolverContext getSolverContext() {
      return solverContext;
    }

    public ShutdownManager getShutdownNotifier() {
      return shutdownMgr;
    }
  }

  private static class ParallelProverStatistics implements Statistics {

    private final LogManager logger;
    private final List<StatisticsEntry> allProverStats = new CopyOnWriteArrayList<>();

    ParallelProverStatistics(LogManager pLogger) {
      logger = checkNotNull(pLogger);
    }

    public synchronized StatisticsEntry getNewSubStatistics(
        String pName, AtomicBoolean pTerminated, AtomicInteger terminatedFirstCount) {
      Collection<Statistics> subStats = new CopyOnWriteArrayList<>();
      StatisticsEntry entry =
          new StatisticsEntry(subStats, pName, pTerminated, terminatedFirstCount);
      allProverStats.add(entry);
      return entry;
    }

    @Override
    public String getName() {
      return "Parallel Prover Statistics";
    }

    @Override
    public void printStatistics(PrintStream out) {
      out.println("Number of solvers used: " + allProverStats.size());
      printSubStatistics(out);
    }

    private void printSubStatistics(PrintStream pOut) {
      for (StatisticsEntry subStats : allProverStats) {
        pOut.println();
        pOut.println();
        String title = "Statistics for: " + subStats.name;
        pOut.println(title);
        pOut.println("=".repeat(title.length()));
        if (subStats.threadCpuTime != null) {
          pOut.println(
              "Time spent in prover thread "
                  + subStats.name
                  + ": "
                  + subStats.threadCpuTime.formatAs(TimeUnit.SECONDS));
        }
        if (subStats.terminatedFirstCount != null) {
          pOut.println(
              "Number of times the solver "
                  + subStats.name
                  + " returned the result first: "
                  + subStats.terminatedFirstCount);
        }

        // Info about currently being terminated
        boolean terminated = subStats.terminated.get();
        if (terminated) {
          for (Statistics s : subStats.subStatistics) {
            StatisticsUtils.printStatistics(s, pOut, logger);
          }
        } else {
          logger.log(
              Level.INFO,
              "Cannot print statistics for",
              subStats.name,
              "because it is still running.");
        }
      }
      pOut.println("\n");
      pOut.println("Other statistics");
      pOut.println("================");
    }
  }
}
