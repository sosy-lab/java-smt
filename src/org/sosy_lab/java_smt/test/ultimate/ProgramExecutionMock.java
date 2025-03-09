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

import de.uni_freiburg.informatik.ultimate.core.lib.results.NoBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import java.util.Collections;

/**
 * This class mocks {@link IProgramExecution}. It can be used in JUnit tests.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @param <T> TraceElementClazz
 * @param <E> ExprClazz
 */
final class ProgramExecutionMock<T, E> implements IProgramExecution<T, E> {

  private final Class<E> mExprClazz;
  private final Class<T> mTraceElementClazz;

  ProgramExecutionMock(final Class<E> exprClazz, final Class<T> traceElementClazz) {
    mExprClazz = exprClazz;
    mTraceElementClazz = traceElementClazz;
  }

  @Override
  public int getLength() {
    return 0;
  }

  @Override
  public AtomicTraceElement<T> getTraceElement(final int index) {
    throw new IndexOutOfBoundsException();
  }

  @Override
  public ProgramState<E> getProgramState(final int index) {
    throw new IndexOutOfBoundsException();
  }

  @Override
  public ProgramState<E> getInitialProgramState() {
    return new ProgramState<>(Collections.emptyMap(), null);
  }

  @Override
  public Class<E> getExpressionClass() {
    return mExprClazz;
  }

  @Override
  public Class<T> getTraceElementClass() {
    return mTraceElementClazz;
  }

  @Override
  public boolean isConcurrent() {
    return false;
  }

  @Override
  public IBacktranslationValueProvider<T, E> getBacktranslationValueProvider() {
    return new NoBacktranslationValueProvider<>();
  }
}
