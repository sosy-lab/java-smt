# JavaSMT Developers Documentation

## Style Guide

The style guide of this project is the Google Java Style:
https://google.github.io/styleguide/javaguide.html

We use the auto-formatting tool, hence before committing run `ant format-diff`
on the staged files in order to format them, or `ant format-source` in order to
format the entire project.

Additionally, refer to the CPAchecker
[style guide](https://github.com/sosy-lab/cpachecker/blob/trunk/doc/StyleGuide.txt)
for more information.

## Continuous Integration

We rely on [Travis][] continuous
integration, which picks up code style violations, compile warnings for both
ECJ and javac, and [FindBugs](http://findbugs.sourceforge.net/) errors.

## Releasing JavaSMT

Currently, releases are pushed to two software repositories:
[Ivy Repository][] and
[Maven Central](http://search.maven.org/).
The release version number is derived from the `git describe` command,
which output is either a git tag (if the release version corresponds exactly
to the tagged commit), or a latest git tag together with a distance measured
in number of commits and a git hash corresponding to the current revision.

### Creating new release numbers

New JavaSMT version is defined by creating a new git tag with a version number.
Git tags should be signed (`git tag -s` command).
When creating a new version number, populate the `CHANGELOG.md` file with the
changes which are exposed by the new release.

[Semantic versioning][] guidelines should be followed when defining a new
version.

### Release to Ivy

If you have write permission to the [Ivy Repository][] you can perform the
release as follows:

 - Symlink the `repository` folder in the JavaSMT to the root of the SVN
    checkout of the Ivy repository.
 - Run the `publish` ANT task.
 - Manually perform the commit in SVN.

### Release to Maven Central

Release to Maven Central is currently not fully automated due to the bug in the
ANT script provided by Maven Central documentation.

The following steps are required:

 - Run the `stage` ANT target.
 - Login to [Nexus Repository Manager](https://oss.sonatype.org/)
 - Run `close` and `release` tasks on the pushed bundle.

Additional instructions are available at the official [OSSRH][] page.

## Releasing Solvers

Publishing of MathSAT5 and Z3 to the [Ivy Repository][] is handled through
JavaSMT.
To publish Z3, run the task `ant publish-z3 -Dz3.path=$Z3_DIR` where `$Z3_DIR` is a
directory with a latest checkout of compiled 64-bit Z3 Solver.

For publishing MathSAT5, a following command-line is required:

```
ant publish-mathsat -Dmathsat.path=$MATHSAT_PATH -Dmathsat.version=$MATHSAT_VERSION
```

Unlike Z3, we produce our own shared object for MathSAT5, and a different
shared object can not be used together with JavaSMT.


[Travis]: https://travis-ci.org/sosy-lab/java-smt
[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
[OSSRH]: http://central.sonatype.org/pages/ossrh-guide.html
[Semantic Versioning]: http://semver.org/
