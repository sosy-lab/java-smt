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

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.Callable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

public class TraceLogger {
  private long id = 0;

  private final Map<Object, String> valueMap = new HashMap<>();
  private final BufferedWriter output;

  TraceLogger(String pFile) {
    // FIXME Check if the file already exists
    try {
      output = Files.newBufferedWriter(Paths.get(pFile), Charset.defaultCharset());
    } catch (IOException e) {
      throw new IllegalArgumentException(e);
    }
  }

  /** Returns a fresh variable. */
  private String newVariable() {
    return "var" + id++;
  }

  /**
   * Bind an object to a variable.
   *
   * <p>Use {@link #toVariable(Object)} to get the variable name for a tracked object
   */
  private void mapVariable(String pVar, Object f) {
    valueMap.putIfAbsent(f, pVar);
  }

  /**
   * Returns the variable name of a tracked object.
   *
   * <p>Use {@link #mapVariable(String, Object)} to bind an object to a variable
   */
  public String toVariable(Object f) {
    return valueMap.get(f);
  }

  /** Add a definition to the log. */
  private void appendDef(String pVar, String pExpr) throws IOException {
    output.append(String.format("var %s = %s;%n", pVar, pExpr));
    output.flush();
  }

  /** Add a statement to the log. */
  private void appendStmt(String pStmt) throws IOException {
    output.append(String.format("%s;%n", pStmt));
    output.flush();
  }

  /** Log an API call with return value. */
  public <R> R logDef(String prefix, String method, Callable<R> closure) {
    String var = newVariable();
    try {
      appendDef(var, prefix + "." + method);
      R f = closure.call();
      mapVariable(var, f);
      return f;

    } catch (Exception e) {
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
      throw new RuntimeException(e);
    }
  }

  /**
   * Takes a {@link org.sosy_lab.java_smt.api.FormulaType} and returns a Java expression to
   * construct this type.
   */
  public <T extends Formula> String printFormulaType(FormulaType<T> pType) {
    if (pType.isIntegerType()) {
      return "FormulaType.IntegerType";
    }
    // FIXME Handle other cases
    throw new IllegalArgumentException("Unsupported formula type: " + pType);
  }
}
