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

package org.sosy_lab.java_smt.utils.Generators;

import org.checkerframework.checker.nullness.qual.Nullable;

/** Exception thrown if there is an error during Generating SMTLIB2. */
public class GeneratorException extends RuntimeException {
  /**
   * Constructs an UnsupportedOperationException with no detail message.
   */
  public GeneratorException() {
  }

  /**
   * Constructs an UnsupportedOperationException with the specified
   * detail message.
   *
   * @param message the detail message
   */
  public GeneratorException(String message) {
    super(message);
  }

  /**
   * Constructs a new exception with the specified detail message and
   * cause.
   *
   * <p>Note that the detail message associated with <code>cause</code> is
   * <i>not</i> automatically incorporated in this exception's detail
   * message.
   *
   * @param  message the detail message (which is saved for later retrieval
   *         by the {@link Throwable#getMessage()} method).
   * @param  cause the cause (which is saved for later retrieval by the
   *         {@link Throwable#getCause()} method).  (A {@code null} value
   *         is permitted, and indicates that the cause is nonexistent or
   *         unknown.)
   * @since 1.5
   */
  public GeneratorException(String message, Throwable cause) {
    super(message, cause);
  }

  /**
   * Constructs a new exception with the specified cause and a detail
   * message of {@code (cause==null ? null : cause.toString())} (which
   * typically contains the class and detail message of {@code cause}).
   * This constructor is useful for exceptions that are little more than
   * wrappers for other throwables (for example, {@link
   * java.security.PrivilegedActionException}).
   *
   * @param  cause the cause (which is saved for later retrieval by the
   *         {@link Throwable#getCause()} method).  (A {@code null} value is
   *         permitted, and indicates that the cause is nonexistent or
   *         unknown.)
   * @since  1.5
   */
  public GeneratorException(Throwable cause) {
    super(cause);
  }

}
