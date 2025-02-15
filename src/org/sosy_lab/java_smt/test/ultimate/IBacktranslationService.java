package org.sosy_lab.java_smt.test.ultimate; /*
                                              * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
                                              * Copyright (C) 2015 University of Freiburg
                                              *
                                              * This file is part of the ULTIMATE Core.
                                              *
                                              * The ULTIMATE Core is free software: you can redistribute it and/or modify
                                              * it under the terms of the GNU Lesser General Public License as published
                                              * by the Free Software Foundation, either version 3 of the License, or
                                              * (at your option) any later version.
                                              *
                                              * The ULTIMATE Core is distributed in the hope that it will be useful,
                                              * but WITHOUT ANY WARRANTY; without even the implied warranty of
                                              * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
                                              * GNU Lesser General Public License for more details.
                                              *
                                              * You should have received a copy of the GNU Lesser General Public License
                                              * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
                                              *
                                              * Additional permission under GNU GPL version 3 section 7:
                                              * If you modify the ULTIMATE Core, or any covered work, by linking
                                              * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
                                              * containing parts covered by the terms of the Eclipse Public License, the
                                              * licensors of the ULTIMATE Core grant you additional permission
                                              * to convey the resulting work.
                                              */

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
  <STE, TTE, SE, TE, SVL, TVL> void addTranslator(
      ITranslator<STE, TTE, SE, TE, SVL, TVL> translator);

  @SuppressWarnings("TypeParameterUnusedInFormals")
  <SE, TE> TE translateExpression(SE expression, Class<SE> sourceExpressionClass);

  /**
   * Translate an expression from the output type to a String.
   *
   * @param expression the expression
   * @param clazz the class
   * @return translated expression
   */
  <SE> String translateExpressionToString(SE expression, Class<SE> clazz);

  <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz);

  <STE> List<String> translateTraceToHumanReadableString(List<STE> trace, Class<STE> clazz);

  <STE, SE> IProgramExecution<?, ?> translateProgramExecution(
      IProgramExecution<STE, SE> programExecution);

  <SE> ProgramState<?> translateProgramState(ProgramState<SE> programState);

  <SE> String translateProgramStateToString(ProgramState<SE> programState);

  <STE, SE> IBacktranslatedCFG<?, ?> translateCFG(IBacktranslatedCFG<?, STE> cfg);

  /**
   * Use this if you want to keep a certain state of the backtranslation chain during toolchain
   * execution.
   */
  IBacktranslationService getTranslationServiceCopy();
}
