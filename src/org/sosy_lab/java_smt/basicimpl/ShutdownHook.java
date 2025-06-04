// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.util.concurrent.atomic.AtomicBoolean;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;

/**
 * A utility class for interrupting a parallel running solver thread.
 *
 * <p>The hook is active directly after its construction until calling the method {@link
 * ShutdownHook#close()} and forwards all shutdown requests to the provided method.
 */
public final class ShutdownHook implements ShutdownRequestListener, AutoCloseable {

  private final ShutdownNotifier contextShutdownNotifier;
  private final @Nullable ShutdownNotifier proverShutdownNotifier;
  private final Runnable interruptCall;

  public ShutdownHook(
      ShutdownNotifier pContextShutdownNotifier,
      @Nullable ShutdownNotifier pProverShutdownNotifier,
      Runnable pInterruptCall) {
    interruptCall = Preconditions.checkNotNull(pInterruptCall);
    contextShutdownNotifier = Preconditions.checkNotNull(pContextShutdownNotifier);
    contextShutdownNotifier.register(this);
    if (pProverShutdownNotifier != null) {
      proverShutdownNotifier = pProverShutdownNotifier;
      proverShutdownNotifier.register(this);
    } else {
      proverShutdownNotifier = null;
    }
  }

  final AtomicBoolean isActiveHook = new AtomicBoolean(true);

  // Due to a small delay in some solvers, interrupts have no effect when it is called too soon,
  // so we repeat cancellation until the solver's method returns and terminates.
  // In that case, we should call #close and terminate this hook.
  @Override
  public void shutdownRequested(@Nullable String reasonUnused) {
    while (isActiveHook.get()) { // flag is reset in #cancelHook
      interruptCall.run();
      try {
        Thread.sleep(10); // let's wait a few steps
      } catch (InterruptedException e) {
        // ignore
      }
    }
  }

  @Override
  public void close() {
    isActiveHook.set(false);
    contextShutdownNotifier.unregister(this);
    if (proverShutdownNotifier != null) {
      proverShutdownNotifier.unregister(this);
    }
  }
}
