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
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

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

  String getMainName() {
    return names.iterator().next();
  }

  @Override
  public int compareTo(CmdLineArgument other) {
    return names.toString().compareTo(other.names.toString());
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    return o instanceof CmdLineArgument && names.equals(((CmdLineArgument) o).names);
  }

  @Override
  public int hashCode() {
    return names.hashCode();
  }

  @Override
  public String toString() {
    String s =
        com.google.common.collect.FluentIterable.from(names)
            .filter(arg -> !CmdLineArguments.isOldStyleArgument(arg))
            .join(Joiner.on("/"));
    if (description.isEmpty()) {
      return s;
    } else {
      return String.format("%1$-20s %2$s", s, description);
    }
  }

  boolean apply(Map<String, String> properties, String currentArg, Iterator<String> argsIt)
      throws InvalidCmdlineArgumentException {
    if (names.contains(currentArg)) {
      apply0(properties, currentArg, argsIt);
      return true;
    }
    return false;
  }

  abstract void apply0(Map<String, String> properties, String currentArg, Iterator<String> argsIt)
      throws InvalidCmdlineArgumentException;

  static class CmdLineArgument1 extends CmdLineArgument {

    private String option;

    CmdLineArgument1(String... pNames) {
      super(pNames);
    }

    CmdLineArgument1 settingOption(String pOption) {
      option = pOption;
      return this;
    }

    @Override
    final void apply0(Map<String, String> properties, String currentArg, Iterator<String> args)
        throws InvalidCmdlineArgumentException {
      if (args.hasNext()) {
        handleArg(properties, args.next());
      } else {
        throw new InvalidCmdlineArgumentException(currentArg + " argument missing.");
      }
    }

    void handleArg(Map<String, String> pProperties, String pArgValue)
        throws InvalidCmdlineArgumentException {
      checkState(option != null);
      putIfNotExistent(pProperties, option, pArgValue);
    }
  }

  static class PropertyAddingCmdLineArgument extends CmdLineArgument {

    private final Map<String, String> additionalIfNotExistentArgs = new HashMap<>();

    PropertyAddingCmdLineArgument(String... pNames) {
      super(pNames);
    }

    @CanIgnoreReturnValue
    PropertyAddingCmdLineArgument settingProperty(String pName, String pValue) {
      additionalIfNotExistentArgs.put(pName, pValue);
      return this;
    }

    @Override
    void apply0(Map<String, String> properties, String currentArg, Iterator<String> args)
        throws InvalidCmdlineArgumentException {
      for (Entry<String, String> e : additionalIfNotExistentArgs.entrySet()) {
        putIfNotExistent(properties, e.getKey(), e.getValue());
      }
    }
  }
}
