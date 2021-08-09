// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt;

import java.util.List;
import org.sosy_lab.common.NativeLibraries;

/**
 * Helper class for loading native libraries. The methods in this class can be overridden and allow
 * the user/application to search for the library binaries in more directories.
 *
 * <p>For Java-based libraries (solvers like SMTInterpol or Princess, and also other dependences),
 * this class is irrelevant and not accessed.
 */
public abstract class LibraryLoader {

  /** This method is called for every library to be loaded. */
  public abstract void loadLibrary(String libraries);

  /** Load several libraries in given order. */
  private void loadLibraries(List<String> libraries) {
    libraries.forEach(this::loadLibrary);
  }

  /**
   * This method loads the given libraries, depending on the operating system.
   *
   * <p>Each list is applied in the given ordering.
   */
  public final void loadLibrary(List<String> linuxLibrary, List<String> windowsLibrary) {
    // we try Linux first, and then Windows.
    // TODO we could simply switch over the OS-name.
    try {
      loadLibraries(linuxLibrary);
    } catch (UnsatisfiedLinkError e1) {
      try {
        loadLibraries(windowsLibrary);
      } catch (UnsatisfiedLinkError e2) {
        e1.addSuppressed(e2);
        throw e1;
      }
    }
  }

  /**
   * This loader does not load any native library. It can be used if the user/application loads
   * native libraries on its own. Please note that native libraries must be loaded in the correct
   * ordering before accessing them, otherwise JavaSMT will throw an {@link UnsatisfiedLinkError}
   * when trying to access native code.
   */
  public static LibraryLoader noopLibraryLoader() {
    return new LibraryLoader() {
      @Override
      public void loadLibrary(String pLibrary) {
        // pass, ignore, dummy, ... the user has to load the library himself.
      }
    };
  }

  /**
   * This loader forwards to the default system-loader of the JVM. It finds native libraries that
   * are installed in the default library paths of the system.
   */
  public static LibraryLoader systemLibraryLoader() {
    return new LibraryLoader() {
      @Override
      public void loadLibrary(String library) {
        System.load(library);
      }
    };
  }

  /**
   * This returned loader searches for native libraries in several directories, for example, the
   * directory of the JAR-file of JavaSMT itself and 'lib/native/[ARCH]-[OS]/'.
   *
   * @see NativeLibraries
   */
  public static LibraryLoader defaultLibraryLoader() {
    return new LibraryLoader() {
      @Override
      public void loadLibrary(String library) {
        NativeLibraries.loadLibrary(library);
      }
    };
  }
}
