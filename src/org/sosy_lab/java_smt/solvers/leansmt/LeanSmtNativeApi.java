// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.function.Consumer;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.api.SolverException;

final class LeanSmtNativeApi {

  private static final ExecutorService CLEANUP_EXECUTOR =
      Executors.newSingleThreadExecutor(
          r -> {
            Thread t = new Thread(r, "leansmt-cleanup");
            t.setDaemon(true);
            return t;
          });
  private static final Object CLEANUP_QUEUE_LOCK = new Object();
  private static boolean cleanupInProgress = false;

  private LeanSmtNativeApi() {}

  static void loadLibrary(Consumer<String> pLoader) {
    Preconditions.checkNotNull(pLoader);
    Path nativeDir = NativeLibraries.getNativeLibraryPath().toAbsolutePath().normalize();
    try {
      pLoader.accept("leansmt_jni");
      configureBundledSolverPathPrefix();
    } catch (UnsatisfiedLinkError error) {
      UnsatisfiedLinkError wrapped =
          new UnsatisfiedLinkError(
              "Failed to load LeanSMT JNI library. "
              + "Expected libleansmt_jni.so in JavaSMT native directory "
              + nativeDir
              + ". "
              + "Original error: "
              + error.getMessage());
      wrapped.initCause(error);
      throw wrapped;
    }
  }

  private static void configureBundledSolverPathPrefix() {
    Path nativeDir = NativeLibraries.getNativeLibraryPath();
    Path cvc5 = nativeDir.resolve("cvc5");
    if (!Files.isExecutable(cvc5)) {
      return;
    }
    try {
      LeanSMT.leansmt_wrapper_set_path_prefix(nativeDir.toString());
    } catch (UnsatisfiedLinkError ignored) {
      // Ignore missing helper and proceed with default process PATH.
    }
  }

  static synchronized void initialize() throws SolverException {
    int status = LeanSMT.leansmt_wrapper_init();
    if (status != LeanSMTConstants.LEANSMT_OK) {
      throw new SolverException(errorOrDefault("Failed to initialize LeanSMT native library"));
    }
  }

  static synchronized boolean isNativeRuntimeInitialized() {
    return LeanSMT.leansmt_wrapper_is_initialized() != 0;
  }

  static synchronized void cleanup() {
    Future<?> queueBarrier;
    synchronized (CLEANUP_QUEUE_LOCK) {
      cleanupInProgress = true;
      queueBarrier = CLEANUP_EXECUTOR.submit(() -> {});
    }
    try {
      awaitCleanupQueueBarrier(queueBarrier);
      LeanSMT.leansmt_wrapper_cleanup();
    } finally {
      synchronized (CLEANUP_QUEUE_LOCK) {
        cleanupInProgress = false;
      }
    }
  }

  private static void awaitCleanupQueueBarrier(Future<?> queueBarrier) {
    try {
      queueBarrier.get(30, TimeUnit.SECONDS);
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    } catch (java.util.concurrent.ExecutionException | java.util.concurrent.TimeoutException e) {
      // Best-effort drain: cleanup still proceeds to avoid wedging shutdown paths.
    }
  }

  private static void drainPendingCleanupQueue() {
    Future<?> queueBarrier;
    synchronized (CLEANUP_QUEUE_LOCK) {
      queueBarrier = CLEANUP_EXECUTOR.submit(() -> {});
    }
    awaitCleanupQueueBarrier(queueBarrier);
  }

  static long createSolverCvc5() throws SolverException {
    // Solver handles may be reused by the native runtime. Make sure older asynchronous deletes
    // have finished before creating a fresh solver, otherwise a queued delete can invalidate the
    // newly returned handle before its first use.
    drainPendingCleanupQueue();
    synchronized (LeanSmtNativeApi.class) {
      BigInteger handle =
          LeanSMT.leansmt_wrapper_create_solver(LeanSMTConstants.LEANSMT_SOLVER_CVC5);
      long solver = toLong(handle);
      if (solver == 0L) {
        throw new SolverException(errorOrDefault("Failed to create LeanSMT solver"));
      }
      return solver;
    }
  }

  static synchronized void deleteSolver(long solver) throws SolverException {
    int status = deleteSolverNative(solver);
    if (status != LeanSMTConstants.LEANSMT_OK) {
      throw new SolverException(errorOrDefault("deleteSolver failed for solver=" + solver));
    }
  }

  private static int deleteSolverNative(long solver) {
    return LeanSMT.leansmt_wrapper_delete_solver(toBigInt(solver));
  }

  /**
   * Best-effort cleanup path for asynchronous teardown.
   *
   * <p>The delete still runs on a background thread, but the actual JNI call is serialized with
   * all other LeanSMT JNI operations. The Lean-side runtime keeps global mutable solver/term
   * tables, so overlapping native deletes with term creation can otherwise invalidate freshly
   * created handles or lose term-table updates.
   */
  private static synchronized void deleteSolverBestEffort(long solver) {
    try {
      deleteSolverNative(solver);
    } catch (RuntimeException | UnsatisfiedLinkError ignored) {
      // best-effort cleanup
    }
  }

  static void deleteSolverAsync(long solver) {
    if (solver == 0L) {
      return;
    }
    synchronized (CLEANUP_QUEUE_LOCK) {
      if (cleanupInProgress) {
        return;
      }
      CLEANUP_EXECUTOR.execute(() -> deleteSolverBestEffort(solver));
    }
  }

  static synchronized void setLogic(long solver, String logic) throws SolverException {
    int status = LeanSMT.leansmt_wrapper_set_logic(toBigInt(solver), logic);
    if (status != LeanSMTConstants.LEANSMT_OK) {
      throw new SolverException(errorOrDefault("Failed to set LeanSMT solver logic"));
    }
  }

  static synchronized long mkBoolVar(long solver, String name) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_bool_var(toBigInt(solver), name), "Failed to create Bool variable");
  }

  static synchronized long mkIntVar(long solver, String name) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_int_var(toBigInt(solver), name), "Failed to create Int variable");
  }

  static synchronized long mkRealVar(long solver, String name) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_real_var(toBigInt(solver), name), "Failed to create Real variable");
  }

  static synchronized long mkBvVar(long solver, String name, int width) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_bv_var(toBigInt(solver), name, width),
        "Failed to create Bitvector variable");
  }

  static synchronized long mkTrue() throws SolverException {
    return requireTerm(LeanSMT.leansmt_wrapper_mk_true(), "Failed to create constant true");
  }

  static synchronized long mkFalse() throws SolverException {
    return requireTerm(LeanSMT.leansmt_wrapper_mk_false(), "Failed to create constant false");
  }

  static synchronized long mkIntConst(long value) throws SolverException {
    return requireTerm(LeanSMT.leansmt_wrapper_mk_int_const(value), "Failed to create Int constant");
  }

  static synchronized long mkRealConst(long num, long den) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_real_const(num, den), "Failed to create Real constant");
  }

  static synchronized long mkBvConst(int width, String value) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_bv_const(width, value), "Failed to create Bitvector constant");
  }

  static synchronized long mkApp1(String op, long t) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_app1(op, toBigInt(t)),
        "Failed to create unary application term");
  }

  static synchronized long mkApp2(String op, long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_app2(op, toBigInt(t1), toBigInt(t2)),
        "Failed to create binary application term");
  }

  static synchronized long mkExtract(long t, int msb, int lsb) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_extract(toBigInt(t), msb, lsb),
        "Failed to create bitvector extract term");
  }

  static synchronized long mkIndexedApp1(String op, int index, long t) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_indexed_app1(op, index, toBigInt(t)),
        "Failed to create indexed unary application term");
  }

  static synchronized long mkNot(long t) throws SolverException {
    return requireTerm(LeanSMT.leansmt_wrapper_mk_not(toBigInt(t)), "Failed to create NOT term");
  }

  static synchronized long mkAnd(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_and(toBigInt(t1), toBigInt(t2)), "Failed to create AND term");
  }

  static synchronized long mkOr(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_or(toBigInt(t1), toBigInt(t2)), "Failed to create OR term");
  }

  static synchronized long mkXor(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_xor(toBigInt(t1), toBigInt(t2)), "Failed to create XOR term");
  }

  static synchronized long mkImplies(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_implies(toBigInt(t1), toBigInt(t2)),
        "Failed to create implication term");
  }

  static synchronized long mkIff(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_iff(toBigInt(t1), toBigInt(t2)), "Failed to create IFF term");
  }

  static synchronized long mkIte(long c, long t, long e) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_ite(toBigInt(c), toBigInt(t), toBigInt(e)),
        "Failed to create ITE term");
  }

  static synchronized long mkEq(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_eq(toBigInt(t1), toBigInt(t2)), "Failed to create EQ term");
  }

  static synchronized long mkDistinct(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_distinct(toBigInt(t1), toBigInt(t2)),
        "Failed to create DISTINCT term");
  }

  static synchronized long mkLt(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_lt(toBigInt(t1), toBigInt(t2)), "Failed to create LT term");
  }

  static synchronized long mkLe(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_le(toBigInt(t1), toBigInt(t2)), "Failed to create LE term");
  }

  static synchronized long mkGt(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_gt(toBigInt(t1), toBigInt(t2)), "Failed to create GT term");
  }

  static synchronized long mkGe(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_ge(toBigInt(t1), toBigInt(t2)), "Failed to create GE term");
  }

  static synchronized long mkAdd(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_add(toBigInt(t1), toBigInt(t2)), "Failed to create ADD term");
  }

  static synchronized long mkSub(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_sub(toBigInt(t1), toBigInt(t2)), "Failed to create SUB term");
  }

  static synchronized long mkMul(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_mul(toBigInt(t1), toBigInt(t2)), "Failed to create MUL term");
  }

  static synchronized long mkDiv(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_div(toBigInt(t1), toBigInt(t2)), "Failed to create DIV term");
  }

  static synchronized long mkMod(long t1, long t2) throws SolverException {
    return requireTerm(
        LeanSMT.leansmt_wrapper_mk_mod(toBigInt(t1), toBigInt(t2)), "Failed to create MOD term");
  }

  static synchronized long mkNeg(long t) throws SolverException {
    return requireTerm(LeanSMT.leansmt_wrapper_mk_neg(toBigInt(t)), "Failed to create NEG term");
  }

  static synchronized void assertTerm(long solver, long term) throws SolverException {
    int status = LeanSMT.leansmt_wrapper_assert(toBigInt(solver), toBigInt(term));
    if (status != LeanSMTConstants.LEANSMT_OK) {
      throw new SolverException(
          errorOrDefault("assertTerm failed for solver=" + solver + ", term=" + term));
    }
  }

  static synchronized int checkSat(long solver) throws SolverException {
    int result = LeanSMT.leansmt_wrapper_check_sat(toBigInt(solver));
    if (result == LeanSMTConstants.LEANSMT_CHECK_ERROR) {
      throw new SolverException(errorOrDefault("LeanSMT reported check-sat error"));
    }
    return result;
  }

  static synchronized String getModel(long solver) throws SolverException {
    String model = LeanSMT.leansmt_wrapper_get_model(toBigInt(solver));
    String error = currentError();
    if (model == null || (model.isEmpty() && error != null && !error.isEmpty())) {
      throw new SolverException(errorOrDefault("Failed to obtain model from LeanSMT"));
    }
    return model;
  }

  static synchronized String getValue(long solver, long term) throws SolverException {
    String value = LeanSMT.leansmt_wrapper_get_value(toBigInt(solver), toBigInt(term));
    String error = currentError();
    if (value == null || (value.isEmpty() && error != null && !error.isEmpty())) {
      throw new SolverException(
          errorOrDefault("Failed to obtain value from LeanSMT for solver=" + solver + ", term=" + term));
    }
    return value;
  }

  private static long requireTerm(BigInteger term, String errorMessage) throws SolverException {
    long value = toLong(term);
    if (value == 0L) {
      throw new SolverException(errorOrDefault(errorMessage));
    }
    return value;
  }

  private static long toLong(BigInteger value) {
    if (value == null) {
      return 0L;
    }
    Preconditions.checkArgument(value.signum() >= 0, "Negative solver handle is invalid");
    return value.longValueExact();
  }

  private static BigInteger toBigInt(long value) {
    Preconditions.checkArgument(value >= 0, "Negative solver handle is invalid");
    return BigInteger.valueOf(value);
  }

  private static String errorOrDefault(String fallback) {
    String error = LeanSMT.leansmt_wrapper_get_error();
    if (error == null || error.isEmpty()) {
      return fallback;
    }
    return fallback + ": " + error;
  }

  static synchronized @Nullable String currentError() {
    return LeanSMT.leansmt_wrapper_get_error();
  }
}
