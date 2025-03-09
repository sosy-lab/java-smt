/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMAT2 Core.
 *
 * The ULTIMAT2 Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMAT2 Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMAT2 Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMAT2 Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMAT2 Core grant you additional permission
 * to convey the resulting work.
 */

package org.sosy_lab.java_smt.test.ultimate;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import java.util.List;

/**
 * {@link IBacktranslationService} contains all {@link ITranslator} instances for the currently
 * running toolchain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
interface IBacktranslationService {

  /**
   * Add a new translator to the backtranslation service. It has to be type-compatible with the
   * existing ones!
   *
   * @param translator translator
   */
  <S, T, S2, T2, S3, T3> void addTranslator(ITranslator<S, T, S2, T2, S3, T3> translator);

  @SuppressWarnings("TypeParameterUnusedInFormals")
  <S2, T2> T2 translateExpression(S2 expression, Class<S2> sourceExpressionClass);

  /**
   * Translate an expression from the output type to a String.
   *
   * @param expression the expression
   * @param clazz the class
   * @return translated expression
   */
  <S2> String translateExpressionToString(S2 expression, Class<S2> clazz);

  <S> List<?> translateTrace(List<S> trace, Class<S> clazz);

  <S> List<String> translateTraceToHumanReadableString(List<S> trace, Class<S> clazz);

  <S, S2> IProgramExecution<?, ?> translateProgramExecution(
      IProgramExecution<S, S2> programExecution);

  <S2> ProgramState<?> translateProgramState(ProgramState<S2> programState);

  <S2> String translateProgramStateToString(ProgramState<S2> programState);

  <S, S2> IBacktranslatedCFG<?, ?> translateCFG(IBacktranslatedCFG<?, S> cfg);

  /**
   * Use this if you want to keep a certain state of the backtranslation chain during toolchain
   * execution.
   */
  IBacktranslationService getTranslationServiceCopy();
}
