<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# JavaSMT Developers Documentation

This file contains hints and documentation for developers,
i.e., for developing JavaSMT, adding code, integrating or updating SMT solvers,
and releasing JavaSMT into a public repository.


## Style Guide

The style guide of this project is the Google Java Style:
https://google.github.io/styleguide/javaguide.html

We use the auto-formatting tool, hence before committing run `ant format-diff`
on the staged files in order to format them, or `ant format-source` in order to
format the entire project.

Additionally, refer to the CPAchecker
[style guide](https://github.com/sosy-lab/cpachecker/blob/trunk/doc/StyleGuide.md)
for more information.


## Continuous Integration

We rely on [GitLab-CI](https://gitlab.com/sosy-lab/software/java-smt/pipelines)
for continuous integration, which picks up code style violations,
compile warnings for both ECJ and javac (for several versions of Java),
[SpotBugs](https://github.com/spotbugs/spotbugs) errors,...


## Releasing JavaSMT

Currently, releases are pushed to two software repositories,
and there is seperate documentation for uploading packages into those repositories:
- [Ivy Repository](http://www.sosy-lab.org/ivy/org.sosy_lab/):
  see [Developers-How-to-Release-into-Ivy](Developers-How-to-Release-into-Ivy.md)
- [Maven Central](http://search.maven.org/):
  see [Developers-How-to-Release-into-Maven.md](Developers-How-to-Release-into-Maven.md).

The release version number is derived from the `git describe` command,
which output is either a git tag (if the release version corresponds exactly
to the tagged commit), or the latest git tag together with a distance measured
in number of commits and a git hash corresponding to the current revision.


### Creating new release numbers

A new JavaSMT version is defined by creating a new git tag with a version number.
Git tags should be signed (`git tag -s` command).
When creating a new version number, populate the `CHANGELOG.md` file with the
changes which are exposed by the new release.

[Semantic versioning](http://semver.org/) guidelines should be followed when defining a new
version.


## Writing Solver Backends

In order to write a solver backend it is sufficient to provide the
implementation for the `SolverContext` interface.
A new backend does not have to implement all the present methods,
and should throw `UnsupportedOperationException` for methods it chooses to ignore.
Abstract classes located inside the `basicimpl` package could be very helpful
for writing new backends.

If the new backend is written inside JavaSMT,
`SolverContextFactory` and the `Solvers` enum should be updated
to include the new solver.
The new solver can be added from outside JavaSMT as well: in that case,
the user might wish to have their own factory which can create
a suitable `SolverContext`.
