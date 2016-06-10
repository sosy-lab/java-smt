/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
/**
 * This wrapper around another theorem prover can be used,
 * if the inner theorem prover does not support addConstraints(f) on an empty stack,
 * i.e. before "push()" was called at least once.
 * The reasons for this behavior of the inner prover might be
 * that the prover should be reused,
 * i.e. the internal stack of formulas must be able to be cleared completely.
 * This is not possible, if the stack is shared,
 * because we cannot use "pop()" to remove constraints from an empty stack.
 */
@javax.annotation.CheckReturnValue
@javax.annotation.ParametersAreNonnullByDefault
@org.sosy_lab.common.annotations.FieldsAreNonnullByDefault
@org.sosy_lab.common.annotations.ReturnValuesAreNonnullByDefault
package org.sosy_lab.solver.reusableStack;
