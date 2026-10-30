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

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.cmdline.CmdLineArguments.putIfNotExistent;

import com.google.common.base.Joiner;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import org.checkerframework.checker.nullness.qual.Nullable;

/**
 * A command-line argument with one or more names, e.g., <code>--solver</code> and <code>-solver
 * </code>. The first name is the main name that is shown in the help message. Sorting and equality
 * are both based on the sequence of names.
 */
abstract class CmdLineArgument implements Comparable<CmdLineArgument> {

  private final ImmutableSet<String> names;
  private String description = "";

  CmdLineArgument(String... pNames) {
    names = ImmutableSet.copyOf(pNames);
  }

  @CanIgnoreReturnValue
  CmdLineArgument withDescription(String pDescription) {
    description = pDescription;
    return this;
  }

  /** The first name given in the constructor. */
  String getMainName() {
    return names.iterator().next();
  }

  @Override
  public int compareTo(CmdLineArgument pOther) {
    // Consistent with equals(): the string of an ImmutableSet lists the names in insertion order.
    return names.toString().compareTo(pOther.names.toString());
  }

  @Override
  public boolean equals(@Nullable Object pOther) {
    if (this == pOther) {
      return true;
    }
    return pOther instanceof CmdLineArgument other && names.asList().equals(other.names.asList());
  }

  @Override
  public int hashCode() {
    return names.asList().hashCode();
  }

  @Override
  public String toString() {
    String s =
        FluentIterable.from(names)
            .filter(pName -> !CmdLineArguments.isOldStyleArgument(pName))
            .join(Joiner.on("/"));
    if (description.isEmpty()) {
      return s;
    } else {
      return String.format("%1$-20s %2$s", s, description);
    }
  }

  /**
   * Applies this argument if it matches the current argument.
   *
   * @return whether the current argument matched one of the names of this argument
   */
  boolean apply(Map<String, String> pProperties, String pCurrentArg, Iterator<String> pArgsIt)
      throws InvalidCmdlineArgumentException {
    if (names.contains(pCurrentArg)) {
      apply0(pProperties, pCurrentArg, pArgsIt);
      return true;
    }
    return false;
  }

  abstract void apply0(
      Map<String, String> pProperties, String pCurrentArg, Iterator<String> pArgsIt)
      throws InvalidCmdlineArgumentException;

  /** A command-line argument with one value that is given as the next argument. */
  static class CmdLineArgument1 extends CmdLineArgument {

    private @Nullable String option;

    CmdLineArgument1(String... pNames) {
      super(pNames);
    }

    /** Sets the name of the option that receives the value of this argument. */
    @CanIgnoreReturnValue
    CmdLineArgument1 settingOption(String pOption) {
      option = pOption;
      return this;
    }

    @Override
    final void apply0(Map<String, String> pProperties, String pCurrentArg, Iterator<String> pArgsIt)
        throws InvalidCmdlineArgumentException {
      if (pArgsIt.hasNext()) {
        handleArg(pProperties, pArgsIt.next());
      } else {
        throw new InvalidCmdlineArgumentException(pCurrentArg + " argument missing.");
      }
    }

    void handleArg(Map<String, String> pProperties, String pArgValue)
        throws InvalidCmdlineArgumentException {
      checkState(option != null, "settingOption() has to be called first");
      putIfNotExistent(pProperties, option, pArgValue);
    }
  }

  /** A command-line argument that sets some properties to fixed values. */
  static class PropertyAddingCmdLineArgument extends CmdLineArgument {

    // Insertion order determines which conflict is reported first.
    private final Map<String, String> additionalIfNotExistentArgs = new LinkedHashMap<>();

    PropertyAddingCmdLineArgument(String... pNames) {
      super(pNames);
    }

    @CanIgnoreReturnValue
    PropertyAddingCmdLineArgument settingProperty(String pName, String pValue) {
      additionalIfNotExistentArgs.put(pName, pValue);
      return this;
    }

    @Override
    void apply0(Map<String, String> pProperties, String pCurrentArg, Iterator<String> pArgsIt)
        throws InvalidCmdlineArgumentException {
      for (Entry<String, String> e : additionalIfNotExistentArgs.entrySet()) {
        putIfNotExistent(pProperties, e.getKey(), e.getValue());
      }
    }
  }
}
