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

We rely on [GitLab-CI][] for continuous integration, which picks up code style violations,
compile warnings for both ECJ and javac (for several versions of Java),
[SpotBugs](https://github.com/spotbugs/spotbugs) errors,...

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
For publishing to Maven Central, we use the [Nexus Repository Manager](https://oss.sonatype.org/).

#### Requirements

Please make sure that all necessary libraries are already released on Maven Central,
before (or at least while) publishing a new version of JavaSMT.
Maven does not check for existing dependencies automatically.

Please make sure that you have a valid user account and configured your local settings accordingly.
For example, insert the following content into `~/.m2/settings.xml`:
```xml
<settings>
  <servers>
    <server>
      <id>ossrh</id>
      <username>USER</username>
      <password>PASSWORD</password>
    </server>
  </servers>
  <profiles>
    <profile>
      <id>gpg</id>
      <properties>
        <gpg.executable>gpg2</gpg.executable>
        <!-- optional <gpg.passphrase>PASSPHRASE</gpg.passphrase> -->
      </properties>
    </profile>
  </profiles>
</settings>
```

#### Publishing

The following steps are required:

 - Run the `stage` ANT target.
   (There is currently no need to change any label from `SNAPSHOT` to `RELEASE` or vice versa,
   as written somewhere in the documentation, because we only produce `RELEASE` versions.)
 - Login to [Nexus Repository Manager](https://oss.sonatype.org/)
   and open the [list of staging repositories](https://oss.sonatype.org/#stagingRepositories).
 - Run `close` and `release` tasks on your pushed bundle
   (see [documentation](http://central.sonatype.org/pages/releasing-the-deployment.html) for details).
 - After some delay (a few hours or days) the release is automatically synced to Maven Central.

Additional instructions are available at the official [OSSRH][] page.

## Releasing Solvers

Before actually releasing a new version of a solver into the public world,
make sure, it is tested sufficiently.
This is one of the most critical steps in JavaSMT development.


### Publishing Z3

We prefer to use the official Z3 binaries,
please build from source only if necessary (e.g., in case of an important bugfix).

To publish Z3, download the **Ubuntu 14.04** binary for the [latest release](https://github.com/Z3Prover/z3/releases)
and unzip it.
Then execute the following command in the JavaSMT directory,
where `$Z3_DIR` is the absolute path of the unpacked Z3 directory
and `$Z3_VERSION` is the version number:
```
ant publish-z3 -Dz3.path=$Z3_DIR/bin -Dz3.version=$Z3_VERSION
```
Finally follow the instructions shown in the message at the end.

As long as [PR #1650](https://github.com/Z3Prover/z3/pull/1650) is not merged,
you need to run the following command before running ant:
```
patchelf --set-soname libz3.so libz3.so
```

To publish Z3 from source, [download it](https://github.com/Z3Prover/z3) and build
it with the following command in its directory on a 64bit Ubuntu 14.04 system
(building on Ubuntu 16.04 introduces unwanted dependencies to new libstdc++ and libgomp versions):

```
./configure --staticlib --java --git-describe && cd build && make -j 2
```
Then execute the following command in the JavaSMT directory, where `$Z3_DIR` is the absolute path of the Z3 directory:
```
ant publish-z3 -Dz3.path=$Z3_DIR/build
```
Finally follow the instructions shown in the message at the end.


### Publishing CVC4

We prefer to use our own CVC4 binaries and Java bindings.

To publish CVC4, checkout the [CVC4 repository](https://github.com/kfriedberger/CVC4).
Then execute the following command in the JavaSMT directory,
where `$CVC4_DIR` is the path to the CVC4 directory
and `$CVC4_VERSION` is the version number:
```
ant publish-cvc4 -Dcvc4.path=$CVC4_DIR -Dcvc4.customRev=$CVC4_VERSION
```
Example:
```
ant publish-cvc4 -Dcvc4.path=../CVC4 -Dcvc4.customRev=1.8-prerelease-2019-10-05
```
Finally follow the instructions shown in the message at the end.


### Publishing Boolector

We prefer to use our own Boolector binaries and Java bindings.

To publish Boolector, checkout the [CVC4 repository](https://github.com/kfriedberger/CVC4).
Then execute the following command in the JavaSMT directory,
where `$BTOR_DIR` is the path to the CVC4 directory
and `$BTOR_VERSION` is the version number:
```
ant publish-boolector -Dboolector.path=$BTOR_DIR -Dboolector.customRev=$BTOR_VERSION
```
Example:
```
ant publish-boolector -Dboolector.path=../boolector -Dboolector.customRev=3.0.0-2019-11-29
```
Finally follow the instructions shown in the message at the end.


### Publishing (Opti)-MathSAT5

For publishing MathSAT5, you need to use a machine with at least GCC 4.9.
First, [download the (reentrant!) binary release](http://mathsat.fbk.eu/download.html), unpack it,
and then execute the following command in the JavaSMT directory,
where `$MATHSAT_PATH` is the path to the MathSAT directory,
and `$MATHSAT_VERSION` is the version number of MathSAT:
```
ant publish-mathsat -Dmathsat.path=$MATHSAT_PATH -Dgmp.path=$GMP_PATH -Dmathsat.version=$MATHSAT_VERSION
```
Finally follow the instructions shown in the message at the end.
The same procedure applies to [OptiMathSAT](http://optimathsat.disi.unitn.it/) solver,
except the publishing command is:

```
ant publish-optimathsat -Dmathsat.path=$OPTIMATHSAT_PATH -Dgmp.path=$GMP_PATH -Dmathsat.version=$OPTIMATHSAT_VERSION
```

### Publishing Princess and SMTInterpol

The scripts for publishing Princess and SMTInterpol are available
at the root of the [Ivy Repository](https://svn.sosy-lab.org/software/ivy).


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
The new solver can be added from outside of JavaSMT as well: in that case,
the user might wish to have their own factory which can create
a suitable `SolverContext`.

[GitLab-CI]: https://gitlab.com/sosy-lab/software/java-smt/pipelines
[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
[OSSRH]: http://central.sonatype.org/pages/ossrh-guide.html
[Semantic Versioning]: http://semver.org/
