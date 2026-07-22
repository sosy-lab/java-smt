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

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSortedSet;
import java.io.PrintStream;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import org.sosy_lab.java_smt.cmdline.CmdLineArgument.CmdLineArgument1;
import org.sosy_lab.java_smt.cmdline.CmdLineArgument.PropertyAddingCmdLineArgument;

/** Processes command-line arguments for JavaSMT. */
public final class CmdLineArguments {

  private CmdLineArguments() {}

  private static final ImmutableSortedSet<CmdLineArgument> CMD_LINE_ARGS =
      ImmutableSortedSet.of(
          new CmdLineArgument1("--solver", "-solver")
              .settingOption("solver.solver")
              .withDescription("Set SMT solver to use"),
          new CmdLineArgument1("--environment", "-environment")
              .settingOption("solver.environment")
              .withDescription("Set the prover environemnt to use"),
          new CmdLineArgument1("--logic", "-logic")
              .settingOption("solver.opensmt.logic")
              .withDescription("Set SMT logic (only for OpenSMT)"),
          new PropertyAddingCmdLineArgument("--help", "-h", "-help")
              .settingProperty("help", "true")
              .withDescription("Print this help message"));

  /**
   * Processes command-line arguments and returns a map of option names to values.
   *
   * @param pArgs Raw command-line arguments
   * @return Map of option names to their values
   * @throws InvalidCmdlineArgumentException if arguments are invalid
   */
  public static Map<String, String> processArguments(String[] pArgs)
      throws InvalidCmdlineArgumentException {
    Preconditions.checkNotNull(pArgs);

    Map<String, String> properties = new HashMap<>();
    Iterator<String> argsIt = Arrays.asList(pArgs).iterator();

    while (argsIt.hasNext()) {
      String arg = argsIt.next();

      boolean found = false;
      for (CmdLineArgument cmd : CMD_LINE_ARGS) {
        if (cmd.apply(properties, arg, argsIt)) {
          found = true;
          break;
        }
      }

      if (!found) {
        if (arg.startsWith("-")) {
          throw new InvalidCmdlineArgumentException("Unknown command-line argument: " + arg);
        } else {
          if (properties.containsKey("smt2.file")) {
            throw new InvalidCmdlineArgumentException(
                "Multiple input files are not supported: "
                    + properties.get("smt2.file")
                    + " and "
                    + arg);
          }
          Path file = Path.of(arg);
          properties.put("smt2.file", file.toString());
        }
      }
    }

    return properties;
  }

  static boolean isOldStyleArgument(String arg) {
    return arg.length() > 2 && arg.startsWith("-") && !arg.startsWith("--");
  }

  private static void printVersion(PrintStream out) {
    out.println();
    Package pkg = CmdLineArguments.class.getPackage();
    String version = pkg != null ? pkg.getImplementationVersion() : "unknown";
    out.println("JavaSMT " + version);
  }

  /**
   * Prints the help message to the given output stream.
   *
   * @param out The output stream to print to
   */
  public static void printHelp(PrintStream out) {
    printVersion(out);
    out.println();
    out.println("Usage: javasmt [options] <file.smt2>");
    out.println("Options:");
    for (CmdLineArgument cmdLineArg : CMD_LINE_ARGS) {
      if (!isOldStyleArgument(cmdLineArg.getMainName())) {
        out.println(" " + cmdLineArg);
      }
    }
    out.println();
    out.println("JavaSMT executes SMT2 files using the selected solver.");
    out.println("javasmt --solver <SOLVER> <file.smt2>");
  }

  static void putIfNotExistent(Map<String, String> properties, String key, String value)
      throws InvalidCmdlineArgumentException {
    if (properties.containsKey(key) && !properties.get(key).equals(value)) {
      throw new InvalidCmdlineArgumentException(
          String.format(
              "Option %s specified twice on command-line with values '%s' and '%s'.",
              key, properties.get(key), value));
    }
    properties.put(key, value);
  }
}
