// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt;

import com.google.common.testing.AbstractPackageSanityTests;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;

public class PackageSanityTest extends AbstractPackageSanityTests {

  {
    setDefault(Configuration.class, Configuration.defaultConfiguration());
    setDefault(ShutdownNotifier.class, ShutdownManager.create().getNotifier());
  }
}
