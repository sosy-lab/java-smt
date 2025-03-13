/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE JUnit Helper Library.
 *
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */

package org.sosy_lab.java_smt.test.ultimate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import java.util.concurrent.CountDownLatch;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
final class ProgressMonitorServiceMock implements IProgressMonitorService {

  private long mDeadline = -1;

  @Override
  public boolean continueProcessing() {
    if (mDeadline == -1) {
      return true;
    }
    return System.currentTimeMillis() < mDeadline;
  }

  @Override
  public IProgressAwareTimer getChildTimer(final long timeout) {
    throw new UnsupportedOperationException();
  }

  @Override
  public IProgressAwareTimer getChildTimer(final double percentage) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void setSubtask(final String task) {
    // mock
  }

  @Override
  public void setDeadline(final long date) {
    mDeadline = date;
  }

  @Override
  public CountDownLatch cancelToolchain() {
    return new CountDownLatch(0);
  }

  @Override
  public IProgressAwareTimer getParent() {
    return null;
  }

  @Override
  public long getDeadline() {
    return mDeadline;
  }

  @Override
  public IProgressAwareTimer getTimer(final long timeout) {
    throw new UnsupportedOperationException();
  }

  @Override
  public long remainingTime() {
    if (mDeadline == -1) {
      return -1;
    }
    return System.currentTimeMillis() - mDeadline;
  }

  @Override
  public IUltimateServiceProvider registerChildTimer(
      final IUltimateServiceProvider services, final IProgressAwareTimer timer) {
    // mock, does not set timer
    return services;
  }
}
