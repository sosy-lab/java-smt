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
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
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

  static void loadLibrary(Consumer<String> loader) {
    loadLibrary(loader, /* allowBundledPathFallback= */ true);
  }

  static void loadLibrary(Consumer<String> loader, boolean allowBundledPathFallback) {
    // Preload transitive runtime dependencies when available; missing entries are tolerated
    // because the final JNI load may still resolve them through platform linker paths.
    for (String dependency : dependencyCandidates()) {
      tryLoadLibraryBestEffort(loader, dependency);
    }

    UnsatisfiedLinkError primaryError =
        loadLibraryWithFallback(loader, "leansmt_jni", allowBundledPathFallback);
    try {
      loadLibraryOrThrow(loader, "libleansmt_jni", allowBundledPathFallback);
      configureBundledSolverPathPrefix();
      return;
    } catch (UnsatisfiedLinkError fallbackError) {
      if (primaryError != null) {
        fallbackError.addSuppressed(primaryError);
      }
      throw new UnsatisfiedLinkError(
          "Failed to load LeanSMT JNI library. "
              + "Expected packaged runtime libs in JavaSMT native lookup paths "
              + "(e.g., libleansmt_jni.so and transitive LeanSMT dependencies). "
              + "Original error: "
              + fallbackError.getMessage());
    }
  }

  private static void configureBundledSolverPathPrefix() {
    Path nativeDir = NativeLibraries.getNativeLibraryPath();
    Set<Path> candidates = new LinkedHashSet<>();
    candidates.add(nativeDir);
    candidates.add(nativeDir.resolve("leansmt-runtime"));
    candidates.add(nativeDir.resolve("leansmt-runtime/bin"));

    for (Path dir : candidates) {
      Path cvc5 = dir.resolve("cvc5");
      if (!Files.isExecutable(cvc5)) {
        continue;
      }
      try {
        if (LeanSMT.leansmt_wrapper_set_path_prefix(dir.toString()) == 0) {
          return;
        }
      } catch (UnsatisfiedLinkError ignored) {
        // Ignore missing helper and proceed with default process PATH.
      }
    }
  }

  private static void tryLoadLibraryBestEffort(Consumer<String> loader, String libName) {
    try {
      loadLibraryOrThrow(loader, libName);
    } catch (UnsatisfiedLinkError ignored) {
      // Optional pre-load for robustness; unresolved entries are retried indirectly
      // when loading the final JNI library.
    }
  }

  private static UnsatisfiedLinkError loadLibraryWithFallback(
      Consumer<String> loader, String libName, boolean allowBundledPathFallback) {
    try {
      loadLibraryOrThrow(loader, libName, allowBundledPathFallback);
      return null;
    } catch (UnsatisfiedLinkError e) {
      return e;
    }
  }

  private static void loadLibraryOrThrow(
      Consumer<String> loader, String libName, boolean allowBundledPathFallback) {
    @Nullable UnsatisfiedLinkError bundledPathError = null;
    if (allowBundledPathFallback) {
      bundledPathError = loadBundledLibraryByAbsolutePath(libName);
      if (bundledPathError == null) {
        return;
      }
    }

    try {
      loader.accept(libName);
      return;
    } catch (UnsatisfiedLinkError namedLoadError) {
      if (bundledPathError != null) {
        bundledPathError.addSuppressed(namedLoadError);
        throw bundledPathError;
      }
      throw namedLoadError;
    }
  }

  private static void loadLibraryOrThrow(Consumer<String> loader, String libName) {
    loadLibraryOrThrow(loader, libName, /* allowBundledPathFallback= */ false);
  }

  private static @Nullable UnsatisfiedLinkError loadBundledLibraryByAbsolutePath(String libName) {
    Set<Path> candidates = new LinkedHashSet<>();
    addDefaultPathCandidates(candidates, libName);

    UnsatisfiedLinkError lastError = null;
    for (Path candidate : candidates) {
      Path absolute = candidate.toAbsolutePath().normalize();
      if (!Files.exists(absolute)) {
        continue;
      }
      try {
        System.load(absolute.toString());
        return null;
      } catch (UnsatisfiedLinkError e) {
        lastError = e;
      }
    }

    if (lastError != null) {
      return lastError;
    }
    return new UnsatisfiedLinkError(
        "Library "
            + libName
            + " was not found in JavaSMT native paths. Checked "
            + candidates.size()
            + " path candidates.");
  }

  private static void addDefaultPathCandidates(Set<Path> candidates, String libName) {
    Path nativeDir = NativeLibraries.getNativeLibraryPath();
    for (String fileName : possibleLibraryFileNames(libName)) {
      candidates.add(nativeDir.resolve(fileName));
    }
  }

  private static Set<String> possibleLibraryFileNames(String libName) {
    Set<String> names = new LinkedHashSet<>();
    String ext = nativeLibraryExtension();
    String bare = withoutLibraryExtension(libName);
    String noPrefix = withoutLibPrefix(bare);

    names.add(bare + ext);
    names.add("lib" + noPrefix + ext);
    if (!libName.endsWith(ext)) {
      names.add(libName);
    }
    return names;
  }

  private static String withoutLibPrefix(String name) {
    if (name.startsWith("lib") && name.length() > 3) {
      return name.substring(3);
    }
    return name;
  }

  private static String withoutLibraryExtension(String name) {
    for (String ext : new String[] {".so", ".dylib", ".dll"}) {
      if (name.endsWith(ext) && name.length() > ext.length()) {
        return name.substring(0, name.length() - ext.length());
      }
    }
    return name;
  }

  private static String nativeLibraryExtension() {
    String os = System.getProperty("os.name", "").toLowerCase(Locale.ROOT);
    if (os.contains("win")) {
      return ".dll";
    } else if (os.contains("mac")) {
      return ".dylib";
    }
    return ".so";
  }

  private static Set<String> dependencyCandidates() {
    LinkedHashSet<String> names = new LinkedHashSet<>();
    names.add("SmtJNI");
    names.add("Smt");
    names.add("Auto");
    names.add("Qq");
    names.add("cvc5");
    names.add("leanshared");
    names.add("libSmtJNI");
    names.add("libSmt");
    names.add("libAuto");
    names.add("libQq");
    names.add("libcvc5");
    names.add("libleanshared");
    return names;
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

  static synchronized long createSolverCvc5() throws SolverException {
    BigInteger handle = LeanSMT.leansmt_wrapper_create_solver(LeanSMTConstants.LEANSMT_SOLVER_CVC5);
    long solver = toLong(handle);
    if (solver == 0L) {
      throw new SolverException(errorOrDefault("Failed to create LeanSMT solver"));
    }
    return solver;
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
   * <p>We intentionally do not synchronize this call on {@link LeanSmtNativeApi}. In some recovery
   * scenarios the native delete can block; holding the class monitor would then stall all future
   * solver operations in this JVM.
   */
  private static void deleteSolverBestEffortNoLock(long solver) {
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
      CLEANUP_EXECUTOR.execute(() -> deleteSolverBestEffortNoLock(solver));
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
    if (model == null) {
      throw new SolverException(errorOrDefault("Failed to obtain model from LeanSMT"));
    }
    return model;
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
