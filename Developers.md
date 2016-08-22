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

### Publishing Z3

To publish Z3, [download it](https://github.com/Z3Prover/z3) and build
it with the following command in its directory on a 64bit system:

```
./configure --staticlib --java --git-describe && cd build && make -j 2
```

Then execute the following command in the JavaSMT directory, where `$Z3_DIR` is the absolute path of the Z3 directory:
```
ant publish-z3 -Dz3.path=$Z3_DIR
```
Finally follow the instructions shown in the message at the end.

### Publishing (Opti)-MathSAT5

For publishing MathSAT5, you need to use a machine with at least GCC 4.9.
First, [download the binary release](http://mathsat.fbk.eu/download.html), unpack it,
and then execute the following command in the JavaSMT directory,
where `$MATHSAT_PATH` is the path to the MathSAT directory,
and `$MATHSAT_VERSION` is the version number of MathSAT:
```
ant publish-mathsat -Dmathsat.path=$MATHSAT_PATH -Dmathsat.version=$MATHSAT_VERSION
```
Finally follow the instructions shown in the message at the end.
The same procedure applies to [OptiMathSAT](http://optimathsat.disi.unitn.it/) solver,
except the publishing command is:

```
ant publish-optimathsat -Dmathsat.path=$OPTIMATHSAT_PATH -Dmathsat.version=$OPTIMATHSAT_VERSION
```

### Publishing Princess and SMTInterpol

The scripts for publishing Princess and SMTInterpol are available
at the root of the [Ivy Repository](https://svn.sosy-lab.org/software/ivy).

[Travis]: https://travis-ci.org/sosy-lab/java-smt
[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
[OSSRH]: http://central.sonatype.org/pages/ossrh-guide.html
[Semantic Versioning]: http://semver.org/
