/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.base.Preconditions;
import com.google.common.base.Throwables;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;
import java.util.concurrent.Callable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

class TraceLogger {
  private final TraceFormulaManager mgr;
  private long id = 0;

  private final Map<Object, String> valueMap = new HashMap<>();
  private final RandomAccessFile output;

  private final Stack<Long> lastLines = new Stack<>();

  TraceLogger(TraceFormulaManager pMgr, String pFile) {
    mgr = pMgr;
    // FIXME Check if the file already exists
    try {
      output = new RandomAccessFile(pFile, "rw");
    } catch (IOException e) {
      throw new IllegalArgumentException(e);
    }
  }

  /** Returns a fresh variable. */
  public String newVariable() {
    return "var" + id++;
  }

  /**
   * Bind an object to a variable.
   *
   * <p>Use {@link #toVariable(Object)} to get the variable name for a tracked object
   */
  public void mapVariable(String pVar, Object f) {
    valueMap.putIfAbsent(f, pVar);
  }

  /** Returns <code>true</code> if the object is tracked. */
  public boolean isTracked(Object f) {
    return valueMap.containsKey(f);
  }

  /**
   * Returns the variable name of a tracked object.
   *
   * <p>Use {@link #mapVariable(String, Object)} to bind an object to a variable
   */
  public String toVariable(Object f) {
    String r = valueMap.get(f);
    Preconditions.checkArgument(r != null, "Object not tracked: %s", f);
    return r;
  }

  /** Add a definition to the log. */
  public void appendDef(String pVar, String pExpr) {
    try {
      lastLines.push(output.length());
      output.write(String.format("var %s = %s;%n", pVar, pExpr).getBytes(StandardCharsets.UTF_8));
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  /** Add a statement to the log. */
  public void appendStmt(String pStmt) {
    try {
      lastLines.push(output.length());
      output.write(String.format("%s;%n", pStmt).getBytes(StandardCharsets.UTF_8));
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  public void undoLast() {
    Preconditions.checkArgument(!lastLines.isEmpty(), "Cannot undo last trace");
    try {
      output.setLength(lastLines.pop());
    } catch (IOException pE) {
      throw new RuntimeException(pE);
    }
  }

  /** Log an API call with return value. */
  public <R extends Formula> R logDef(String prefix, String method, Callable<R> closure) {
    String var = newVariable();
    try {
      appendDef(var, prefix + "." + method);
      R f = closure.call();
      if (isTracked(f)) {
        undoLast();
        return f;
      } else {
        mapVariable(var, f);
        return mgr.rebuild(f);
      }
    } catch (Exception e) {
      Throwables.throwIfUnchecked(e);
      throw new RuntimeException(e);
    }
  }

  /**
   * Variant of {@link #logDef(String, String, Callable)} that will always keep the call in the log.
   *
   * <p>Use this version if the called function has side effects
   */
  public <R> R logDefKeep(String prefix, String method, Callable<R> closure) {
    String var = newVariable();
    try {
      appendDef(var, prefix + "." + method);
      R f = closure.call();
      mapVariable(var, f);
      return f;
    } catch (Exception e) {
      Throwables.throwIfUnchecked(e);
      throw new RuntimeException(e);
    }
  }

  /**
   * Variant of {@link #logDef(String, String, Callable)} that will always remove the call from the
   * log after it returned successfully.
   */
  public <R> R logDefDiscard(String prefix, String method, Callable<R> closure) {
    String var = newVariable();
    try {
      appendDef(var, prefix + "." + method);
      R f = closure.call();
      undoLast();
      return f;
    } catch (Exception e) {
      Throwables.throwIfUnchecked(e);
      throw new RuntimeException(e);
    }
  }

  /** Just like {@link Runnable}, but allows checked exceptions. */
  public interface CheckedRunnable {
    void run() throws Exception;
  }

  /** Log an API call without return value. */
  public void logStmt(String prefix, String method, CheckedRunnable closure) {
    try {
      appendStmt(prefix + "." + method);
      closure.run();
    } catch (Exception e) {
      Throwables.throwIfUnchecked(e);
      throw new RuntimeException(e);
    }
  }

  /**
   * Variant of {@link #logStmt(String, String, CheckedRunnable)} that will remove the call from the
   * log after it returned successfully.
   */
  public void logStmtDiscard(String prefix, String method, CheckedRunnable closure) {
    try {
      appendStmt(prefix + "." + method);
      closure.run();
      undoLast();
    } catch (Exception e) {
      Throwables.throwIfUnchecked(e);
      throw new RuntimeException(e);
    }
  }

  /**
   * Takes a {@link org.sosy_lab.java_smt.api.FormulaType} and returns a Java expression to
   * construct this type.
   */
  public <T extends Formula> String printFormulaType(FormulaType<T> pType) {
    if (pType.isBooleanType()) {
      return "FormulaType.BooleanType";
    }
    if (pType.isIntegerType()) {
      return "FormulaType.IntegerType";
    }
    if (pType.isRationalType()) {
      return "FormulaType.RationalType";
    }
    if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrayType = (ArrayFormulaType<?, ?>) pType;
      return String.format(
          "FormulaType.getArrayType(%s, %s)",
          printFormulaType(arrayType.getIndexType()), printFormulaType(arrayType.getElementType()));
    }
    if (pType.isBitvectorType()) {
      BitvectorType bvType = (BitvectorType) pType;
      return String.format("FormulaType.getBitvectorTypeWithSize(%s)", bvType.getSize());
    }
    if (pType.isFloatingPointType()) {
      FloatingPointType fpType = (FloatingPointType) pType;
      return String.format(
          "FormulaType.getFloatingPointType(%s, %s)",
          fpType.getExponentSize(), fpType.getMantissaSize());
    }
    // FIXME Handle other cases
    throw new IllegalArgumentException("Unsupported formula type: " + pType);
  }
}
