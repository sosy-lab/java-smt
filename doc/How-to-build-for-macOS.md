<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Building solver binaries for macOS

We currently can't provide binaries for all supported solvers on macOS. However, it's often
possible to build the necessary binaries from source, and we try to include a simple build
script wherever possible

## Yices

To build the Yices binaries, we first need some build dependencies and GMP, which can all be
installed via Homebrew:

```shell
brew update
brew install gperf lcov autoconf automake libtool
brew install gmp
```

Then, we build the Yices2 binaries by running the build script included with JavaSMT:

```shell
git clone git@github.com:sosy-lab/java-smt.git
cd java-smt
ant publish-yices2-macOS
```

The script will build several dependencies before compiling Yices and may run for up to 10
minutes. Once it's finished the binary `libyices2java.dylib` can be found under `lib/native`.
Depending on your system architecture, it will be either in the `arm64-macos` (ARM) or
`x64_64-macos` (Intel) folder

You can then either copy the binary to your project folder, or
set `DYLD_LIBRARY_PATH` to include the binary folder to make sure Yices will be found when
running JavaSMT