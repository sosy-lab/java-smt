// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

/* some systems do not have newest memcpy@@GLIBC_2.14 - stay with old good one */
asm(".symver memcpy, memcpy@GLIBC_2.2.5");

void *__wrap_memcpy(void *dest, const void *src, size_t n) {
    return memcpy(dest, src, n);
}
