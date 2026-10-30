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

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedSet;
import com.google.common.collect.Iterators;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.cmdline.CmdLineArgument.CmdLineArgument1;
import org.sosy_lab.java_smt.cmdline.CmdLineArgument.PropertyAddingCmdLineArgument;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/** Processes command-line arguments for JavaSMT. */
public final class CmdLineArguments {

  private CmdLineArguments() {}

  // Keys in the map returned by processArguments()
  static final String SOLVER_OPTION = "solver.solver";
  static final String OPENSMT_LOGIC_OPTION = "solver.opensmt.logic";
  static final String Z3_LOGIC_OPTION = "solver.z3.logic";
  static final String FILE_OPTION = "smt2.file";
  static final String HELP_OPTION = "help";

  /** The command-line argument that requests the help message. */
  static final String HELP_ARGUMENT = "--help";

  /** Solvers that cannot parse SMT-LIB2 input, see {@link #printHelp}. */
  private static final ImmutableSet<Solvers> SOLVERS_WITHOUT_PARSER =
      ImmutableSet.of(Solvers.BOOLECTOR, Solvers.CVC4, Solvers.YICES2);

  /** Solvers that have an option for the logic, i.e., for which --logic is effective. */
  static final ImmutableSet<Solvers> SOLVERS_WITH_LOGIC_OPTION =
      ImmutableSet.of(Solvers.OPENSMT, Solvers.Z3);

  private static final ImmutableSortedSet<CmdLineArgument> CMD_LINE_ARGS =
      ImmutableSortedSet.of(
          new CmdLineArgument1("--solver", "-solver")
              .settingOption(SOLVER_OPTION)
              .withDescription("Set the SMT solver, default: " + JavaSMTMain.DEFAULT_SOLVER),
          new CmdLineArgument1("--logic", "-logic")
              .settingOption(OPENSMT_LOGIC_OPTION)
              .withDescription("Set the logic for OpenSMT and Z3, ignored for other solvers"),
          new PropertyAddingCmdLineArgument(HELP_ARGUMENT, "-h", "-help")
              .settingProperty(HELP_OPTION, "true")
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
    Iterator<String> argsIt = Iterators.forArray(pArgs);

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
          if (properties.containsKey(FILE_OPTION)) {
            throw new InvalidCmdlineArgumentException(
                "Multiple input files are not supported: "
                    + properties.get(FILE_OPTION)
                    + " and "
                    + arg);
          }
          final Path file;
          try {
            file = Path.of(arg);
          } catch (InvalidPathException e) {
            throw new InvalidCmdlineArgumentException("Invalid path of SMT2 file: " + arg, e);
          }
          properties.put(FILE_OPTION, file.toString());
        }
      }
    }

    // OpenSMT and Z3 read the logic from different options, and --logic sets both of them.
    // Only the solver that is used reads its option, the other one is never looked at.
    String logic = properties.get(OPENSMT_LOGIC_OPTION);
    if (logic != null) {
      properties.put(Z3_LOGIC_OPTION, logic);
    }

    return properties;
  }

  /** Whether the argument has the old single-dash style, e.g., <code>-solver</code>. */
  static boolean isOldStyleArgument(String pArg) {
    return pArg.length() > 2 && pArg.startsWith("-") && !pArg.startsWith("--");
  }

  private static void printVersion(Appendable pOut) {
    Output.println(pOut, "");
    // The version is only available from the manifest of the JAR, not when running from bin/.
    final String version;
    Package pkg = CmdLineArguments.class.getPackage();
    if (pkg != null && pkg.getImplementationVersion() != null) {
      version = pkg.getImplementationVersion();
    } else {
      version = "unknown";
    }
    Output.println(pOut, "JavaSMT " + version);
  }

  /**
   * Prints the help message, including the allowed arguments and the restrictions on the input, to
   * the given output.
   *
   * @param pOut The output to print to
   */
  public static void printHelp(Appendable pOut) {
    printVersion(pOut);
    Output.println(pOut, "");
    Output.println(pOut, "Usage: javasmt [--solver SOLVER] [--logic LOGIC] <file.smt2>");
    Output.println(pOut, "Options:");
    for (CmdLineArgument cmdLineArg : CMD_LINE_ARGS) {
      if (!isOldStyleArgument(cmdLineArg.getMainName())) {
        Output.println(pOut, " " + cmdLineArg);
      }
    }
    Output.println(pOut, "");
    Output.println(
        pOut,
        "JavaSMT checks the satisfiability of the assertions in the given SMT-LIB2 file with the");
    Output.println(
        pOut, "selected solver and prints exactly one of sat, unsat, or unknown on stdout, or");
    Output.println(
        pOut, "nothing in case of an error. All other output goes to stderr. The exit code is 0");
    Output.println(pOut, "for sat and unsat, and 1 for unknown and for all errors.");
    Output.println(pOut, "");
    Output.println(pOut, "Solvers: " + Joiner.on(", ").join(Solvers.values()));
    Output.println(
        pOut,
        "Solvers without a parser for SMT-LIB2 input cannot be used: "
            + Joiner.on(", ").join(SOLVERS_WITHOUT_PARSER));
    Output.println(pOut, "Logics for OpenSMT: " + Joiner.on(", ").join(Logics.values()));
    Output.println(pOut, "Logics for Z3: the SMT-LIB2 logics, e.g., QF_LIA, or ALL, the default.");
    Output.println(
        pOut, "Arguments starting with -X, e.g., -Xmx4g, are passed to the JVM by the launcher.");
    Output.println(pOut, "");
    Output.println(pOut, "Restrictions on the SMT-LIB2 file:");
    Output.println(pOut, " - It has to contain exactly one (check-sat) command.");
    Output.println(pOut, " - All assertions have to precede the (check-sat) command.");
    Output.println(pOut, " - (check-sat-assuming ...) is not supported.");
    Output.println(
        pOut, " - (push ...), (pop ...), (reset), and (reset-assertions) are not supported.");
    Output.println(pOut, " - (exit) is only allowed as the last command.");
    Output.println(
        pOut, " - Only declarations, definitions, and assertions are evaluated, other commands");
    Output.println(pOut, "   such as (set-option ...) or (get-model) are ignored.");
    Output.println(pOut, " - (set-logic ...) is ignored as well, use --logic to select the logic.");
  }

  static void putIfNotExistent(Map<String, String> pProperties, String pKey, String pValue)
      throws InvalidCmdlineArgumentException {
    if (pProperties.containsKey(pKey) && !pProperties.get(pKey).equals(pValue)) {
      throw new InvalidCmdlineArgumentException(
          String.format(
              "Option %s specified twice on command-line with values '%s' and '%s'.",
              pKey, pProperties.get(pKey), pValue));
    }
    pProperties.put(pKey, pValue);
  }
}
