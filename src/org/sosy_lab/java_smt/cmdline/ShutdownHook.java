/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.cmdline;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.common.ShutdownManager;

/**
 * Shutdown hook for the JVM that requests a shutdown from the solver if the JVM is terminated while
 * the solver is running, e.g., because Ctrl+C was pressed or SIGTERM was sent. The hook then keeps
 * the JVM alive for a grace period, such that the main thread can report <code>unknown</code> and
 * close the solver.
 */
final class ShutdownHook extends Thread {

  /**
   * How long to wait for the main thread after a shutdown request. Solvers are not guaranteed to
   * respond to shutdown requests, see {@link org.sosy_lab.java_smt.api.ProverEnvironment}.
   */
  private static final long GRACE_PERIOD_MILLIS = 10_000;

  private final ShutdownManager shutdownManager;
  private final Thread mainThread;

  // Whether this hook should act at all. Monotonic (true -> false).
  private volatile boolean enabled = true;

  /**
   * Create a shutdown hook. This constructor needs to be called from the thread that runs the
   * solver, as the hook waits for this thread to finish.
   */
  ShutdownHook(ShutdownManager pShutdownManager) {
    super("Shutdown Hook");
    shutdownManager = checkNotNull(pShutdownManager);
    mainThread = Thread.currentThread();
  }

  /**
   * Disable this hook once the result is reported, such that it neither requests a shutdown nor
   * delays the exit of the JVM. Must be called before {@link System#exit(int)}, otherwise the exit
   * would wait for this hook, which waits for the main thread that is blocked in the exit.
   */
  void disableAndStop() {
    enabled = false;
    interrupt(); // in case it is already waiting for the main thread
  }

  @SuppressWarnings("ThreadJoinLoop") // interrupt is used on purpose by disableAndStop()
  @Override
  public void run() {
    if (enabled && mainThread.isAlive()) {
      shutdownManager.requestShutdown(
          "The JVM is shutting down, probably because Ctrl+C was pressed.");
      try {
        mainThread.join(GRACE_PERIOD_MILLIS);
      } catch (InterruptedException expected) {
        // disableAndStop() was called, the result is reported
      }
    }
  }
}
