// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/**
 * This wrapper around another theorem prover can be used, if the inner theorem prover does not
 * support addConstraints(f) on an empty stack, i.e. before "push()" was called at least once. The
 * reasons for this behavior of the inner prover might be that the prover should be reused, i.e. the
 * internal stack of formulas must be able to be cleared completely. This is not possible, if the
 * stack is shared, because we cannot use "pop()" to remove constraints from an empty stack.
 */
@com.google.errorprone.annotations.CheckReturnValue
@javax.annotation.ParametersAreNonnullByDefault
@org.sosy_lab.common.annotations.FieldsAreNonnullByDefault
@org.sosy_lab.common.annotations.ReturnValuesAreNonnullByDefault
package org.sosy_lab.java_smt.basicimpl.reusableStack;
