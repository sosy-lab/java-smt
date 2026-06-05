<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Release JavaSMT or Solver Binaries to Ivy

Please read the hints on release in the [developer documentation](Developers.md) first.

## Releasing JavaSMT

If you have write permission to the [Ivy Repository][] you can perform the release as follows:

 - Symlink the `repository` folder in the JavaSMT to the root of the SVN checkout of the Ivy repository.
 - Run the `publish` ANT task and inspect the files for correctness and completeness!
 - Manually perform the commit in SVN.


## Releasing Solvers

Before actually releasing a new version of a solver into the public world,
make sure, it is tested sufficiently.
This is one of the most critical steps in JavaSMT development.


### Publishing Princess and SMTInterpol

By default, Java-based solvers are copied over from Maven Central.
Please execute the following in the root directory of the [Ivy Repository][]:
```bash
ant install -Dorganisation=io.github.uuverifiers -Dmodule=princess_2.13 -Drevision=????-??-??
```
```bash
ant install -Dorganisation=de.uni-freiburg.informatik.ultimate -Dmodule=smtinterpol 
-Drevision=?.?-???-g???????
```

Potentially outdated:
For manually uploading a Java-based solver to the [Ivy Repository][],
there are scripts for publishing available at the root of the [Ivy Repository](https://svn.sosy-lab.org/software/ivy).


### Publishing Z3

We prefer to use the official Z3 binaries,
please build from source only if necessary (e.g., in case of an important bugfix).

### From official binaries (for Linux, Windows, and OSX)

To publish Z3, download the **Linux**, **Windows**, and **OSX** binary (for both, x64 and ARM64 architecture)
and the sources (for JavaDoc) for the [latest release](https://github.com/Z3Prover/z3/releases) and unzip them.
For example, the directory structure can look like this:
```
z3/                                 // <-- parent directory
 |-- z3-4.13.3-arm64-glibc-2.34/    // <-- unpacked release artifact
 |-- z3-4.13.3-arm64-osx-13.7/
 |-- z3-4.13.3-arm64-win/
 |-- z3-4.13.3-x64-glibc-2.35/
 |-- z3-4.13.3-x64-osx-13.7/
 |-- z3-4.13.3-x64-win/
 |-- z3-z3-4.13.3/                  // <-- sources directory used as 'z3.path'
```

You can prepare the Z3 Java sources on an arbitrary system, as we only prepare 
Java sources and JavaDoc for the bindings, but do not compile any native library.
This only depends on a Python3 environment and Java 17 or later.
For simple usage, we provide a Docker definition/environment under `/docker`, in which the following command can be run.

In the unpacked sources directory, prepare Java sources via `python3 scripts/mk_make.py --java`.
Then execute the following command in the JavaSMT directory,
where `$Z3_DIR` is the path of the sources directory and `$Z3_VERSION` is the version number:
```bash
ant publish-z3 -Dz3.path=$Z3_DIR -Dz3.version=$Z3_VERSION
```
Example:
```bash
ant publish-z3 -Dz3.path=/workspace/solvers/z3/z3-z3-4.13.3 -Dz3.version=4.13.3
```
Finally, follow the instructions shown in the message at the end.


#### Optional (from source for Linux target with older GLIBC)

This step is for the following use case:
Newer releases of Z3 depend on newer versions of GLIBC (>=v2.35),
so we want to compile the Linux release on our own and then combine it with the provided libraries for Windows and macOS.
We follow the steps from above, download and unpack the given zip archives for all platforms, except the Linux release (where the GLIBC is too new).
For simple usage, we provide a Docker definition/environment under `/docker` (based on Ubuntu 18.04 with GLIBC 2.27),
in which the following build command can be run in the unpacked source directory:
```bash
python3 scripts/mk_make.py --java && cd build && make -j 2
```
Afterward, copy the native libraries for Linux (`libz3.so` and `libz3java.so`) from the directory 
`./build` into `./bin` (if needed, adjust the directory to match the x64 or arm64 path for Linux).
Then perform as written above with adding the additional pre-compiled binaries for other operating systems,
and publish the directory `./bin` with an ant command like the one from above:
```bash
ant publish-z3 -Dz3.path=$Z3_DIR -Dz3.version=$Z3_VERSION-glibc_2.27
```


### Publishing Z3 v4.5.0 (aka LegacyZ3)

The legacy version of Z3 (v4.5.0) is still integrated,
because it provides support for Craig interpolation in Z3.
This feature was removed in some later version of Z3.

For publishing the legacy version of Z3 (v4.5.0),
please follow the instructions in the `lib/native/source/z3-4.5.0/README.md` file,
which explains how to patch the original Z3 v4.5.0 source code
so that the Java package names include the string `legacy`.
This is necessary to avoid conflicts with later versions of Z3.

These steps can be performed in a Docker environment based on Ubuntu 18.04,
which is provided under `/docker` in the JavaSMT repository.
After building the patched Z3 v4.5.0 version,
you can publish it with the following command in the JavaSMT directory:
```bash
ant publish-z3-legacy -Dz3.path=<Z3_PATH> -Dz3.customRev=<VERSION>
```

Example:
```bash
ant publish-z3-legacy -Dz3.path=../solvers/z3/z3 -Dz3.customRev=4.5.0
```

### Publishing CVC4

We use the Docker image with Ubuntu 18.04 for publishing CVC4.
Please manually add two additional dependencies before running the build script:

```bash
pip3 install toml
apt-get install antlr3 libantlr3c-dev
```

Then run the build script to publish the bindings:

```bash
ant publish-cvc4 -Dcvc4.path=/workspace/CVC4-archived -Dcvc4.customRev=1.8.1
```

### Publishing CVC5

We prefer to use the official CVC5 binaries, please build from source only if necessary (e.g., in
case of an important bugfix). The binaries can be fetched and repackaged fully automatically.
CVC5 provides releases on GitHub (https://github.com/cvc5/cvc5/releases) for multiple platform,
including Linux, Windows, and macOS (x64 and arm64). 
The releases on GitHub include versioned releases and also daily builds for the last two days.
Our build-script downloads daily build artifacts, extracts the native libraries and Java bindings, 
and publishes them for JavaSMT.

To publish a daily version of CVC5, execute the following command in the JavaSMT directory:
```bash
ant publish-cvc5 -Dcvc5.version=$CVC5_VERSION
```

Where `CVC5_VERSION` must match one of the daily releases from
their [GitHub](https://github.com/cvc5/cvc5/releases/tag/latest) website

Example:
```bash
ant publish-cvc5 -Dcvc5.version=2025-03-31-34518c3
```

During the build process, our script automatically fetches binaries for Windows, Linux, and
maxOS on x64 and arm64 and repackages them to be used in JavaSMT.


### Publishing OpenSMT

We prefer to use our own OpenSMT binaries and SWIG-based Java bindings.
We prefer to build directly on Ubuntu 22.04, where CMake, SWIG, and GCC are sufficiently up-to-date.
For simple usage, we provide a Docker definition/environment under `/docker`,
in which the following command can be run.

When using the Docker container, dependencies for GMP and JDK are already included for several platforms
and include the following directories:
- `/dependencies/gmp-6.2.1/install` for `x64-linux` and `arm64-linux`, and
- `/dependencies/jdk17-linux-aarch64`.

If you want to build your own dependencies, please apply the following steps:
Provide GMP from http://gmplib.org/ in version 6.3.0 (version 6.2.1 also works) and build GMP:
- For linux-x64 in directory $GMP_DIR_LINUX_X64:
  ```bash
  ./configure --enable-cxx --with-pic --disable-shared --enable-static --enable-fat
  make -j4
  ```
- For linux-arm64 in directory $GMP_DIR_LINUX_ARM64:
  ```bash
  ./configure --enable-cxx --with-pic --disable-shared --enable-static --enable-fat \
  --host=aarch64-linux-gnu \
  CC=aarch64-linux-gnu-gcc CXX=aarch64-linux-gnu-g++ LD=aarch64-linux-gnu-ld
  make -j4
  ```
For linux-arm64, provide JNI headers in a reasonable LTS version.
Download the zip archive from https://jdk.java.net/ and unpack it into $JDK_DIR_LINUX_ARM64
(e.g., https://download.java.net/java/GA/jdk17.0.2/dfd4a8d0985749f896bed50d7138ee7f/8/GPL/openjdk-17.0.2_linux-aarch64_bin.tar.gz).

To publish OpenSMT, checkout the [OpenSMT repository](https://github.com/usi-verification-and-security/opensmt).
Then execute the following command in the JavaSMT directory:
```bash
ant publish-opensmt \
    -Dopensmt.path=$OPENSMT_DIR \
    -Dopensmt.customRev=$VERSION \
    -Dgmp-linux-x64.path=$GMP_DIR_LINUX_X64 \
    -Dgmp-linux-arm64.path=$GMP_DIR_LINUX_ARM64 \
    -Djdk-linux-arm64.path=$JDK_DIR_LINUX_ARM64
```
Example:
```bash
ant publish-opensmt \
    -Dopensmt.path=/workspace/solvers/opensmt/opensmt \
    -Dopensmt.customRev=2.9.2 \
    -Dgmp-linux-x64.path=/dependencies/gmp-6.3.0/install/x64-linux \
    -Dgmp-linux-arm64.path=/dependencies/gmp-6.3.0/install/arm64-linux \
    -Djdk-linux-arm64.path=/dependencies/jdk17-linux-aarch64
```
The build scripts for OpenSMT ... :
- run for about 20 minutes (we build everything from scratch, two times).
- download Google-based test components (requires internet access).
- append the git revision of OpenSMT.
- produce two Linux (x64 and arm64) libraries, and publish them.

Finally, follow the instructions shown in the message at the end of the command.
The instructions for publication via SVN into the Ivy repository are not intended to be executed in the Docker environment,
but in the normal system environment, where some testing can be applied by the developer before the commit.


### Publishing Boolector

We prefer to use our own Boolector binaries and Java bindings.
Boolector's dependencies, mainly Minisat, requires GCC version 7 and does not yet compile with newer compilers.
We prefer to build directly on Ubuntu 18.04, where gcc-7 is the default compiler.
It should also be possible to set environment varables like CC=gcc-7 on newer systems.
For simple usage, we provide a Docker definition/environment under `/docker`,
in which the following command can be run.

To publish Boolector, checkout the [Boolector repository](https://github.com/Boolector/boolector).
Then execute the following command in the JavaSMT directory,
where `$BTOR_DIR` is the path to the Boolector directory and `$BTOR_VERSION` is the version number:
```bash
CC=gcc-7 ant publish-boolector -Dboolector.path=$BTOR_DIR -Dboolector.customRev=$BTOR_VERSION
```
Example:
```bash
ant publish-boolector -Dboolector.path=../boolector -Dboolector.customRev=3.2.2
```
Our build script will automatically append the git revision of Boolector, if available.

Finally, follow the instructions shown in the message at the end of the command.
The instructions for publication via SVN into the Ivy repository are not intended to be executed in the Docker environment,
but in the normal system environment, where some testing can be applied by the developer before the commit.


### Publishing Bitwuzla

We prefer to use our own Bitwuzla binaries and SWIG-based Java bindings.
We prefer to build directly on Ubuntu 22.04, where CMake, SWIG, and Meson are sufficiently up-to-date.
For simple usage, we provide a Docker definition/environment under `/docker`,
in which the following command can be run. While it's possible to build without the container, some
paths in the build script (`build/build-publish-solvers/solver-bitwuzla.xml`) are hardwired
and would have to be updated first

To publish Bitwuzla, checkout the [Bitwuzla repository](https://github.com/bitwuzla/bitwuzla). Then
execute the following command in the JavaSMT directory:
```bash
ant bitwuzla-generate-jni -Dbitwuzla.path=/workspace/bitwuzla
```

This will rebuild the JNI bindings for Bitwuzla with SWIG. To see the changes go to
`lib/source/native/libbitwuzla`, and then compare with git:

```bash
cd lib/source/libbitwuzla
git status
git diff
```

Also check if there are any new Java files in the `src` folder under 
`lib/source/native/libbitwuzla`. Normally, the changes for an update should be minimal, and
there should be no new files. If you find any `SWIGTYPE_p` classes, it means SWIG ran into a
class that it didn't understand, and simply created an opaque wrapper for the C++ object. Most
of the time, this is not what we want, and some updates to the SWIG script (`bitwuzla.i`) will
be necessary. 

While editing `bitwuzla.i`, you can rerun the command from above at any time to check your changes.
The command will also produce an updated patch containing the latest changes.
If there are more changes than just whitespace and timestamps, please commit the changes to JavaSMT.

Often, the problem is a new method that was added to the API with an argument or return type that 
is not handled correctly. The simple solution may then be to remove the new method by adding an
`%ignore` to the SWIG script. If the method is actually interesting to us, and we want to keep it,
it might be necessary to instantiate a `%template` or otherwise wrap the method to help SWIG handle
the types.

Often there will be no new files left once `bitwuzla.i` has been fixed. If there are still new
files left, they have to be added to git. Also remember to add the copyright header to all new
files, and make sure that new classes implement the `Reference` interface to allow tracking for
garbage collection. Normal classes can extend `AbstractReference` for convenience, see `Term.
java` for an example. If the class wraps a `std::vector` or similar, it will already extend a
different class. In that case the `Reference` interface can be implemented similar to how it's
done in `Vector_Int.java`.

Once the SWIG script has been fully fixed, we "commit" our changes, and build the actual binaries:
```bash
ant publish-bitwuzla \
    -Dbitwuzla.path=/workspace/bitwuzla \
    -Dbitwuzla.customRev=0.9.0
```

This command will first try to build the Java code for the bindings. If there is an error, it
aborts, and you can go back to the last step to fix the generated code. Otherwise, the script
continues to build binaries for all platforms, which can take several minutes. Dependencies like
GMP are handled automatically, and the script will add a git hash to the `customRev` version
string before finally publishing the binaries.

Finally, follow the instructions shown in the message at the end of the command.
The instructions for publication via SVN into the Ivy repository are not intended to be executed
in the Docker environment, but in the normal system environment, where some testing can be 
applied by the developer before the commit.


### Publishing (Opti)-MathSAT5

We publish MathSAT for Linux (x64 and arm64) and Windows (x64) systems at once.
The build process can fully be done on a Linux system, 
and requires several dependencies, such as gcc, x86_64-w64-mingw32-gcc, and aarch64-linux-gnu-gcc.
We prefer to use the Docker container based on Ubuntu 24.04
for compiling the dependencies and assembling the libraries.
Since MathSAT5 5.6.12, using Ubuntu 18.04 or 22.04 with older GLIBC no longer works!

First, [download the (reentrant!) Linux and Windows64 binary release](http://mathsat.fbk.eu/download.html) in the same version, unpack them.
Then provide the necessary dependencies (GMP/JDK for Linux (x64 and arm64) and GMP/JDK for Windows (x64))
as described in the compilation scripts (see `lib/native/source/libmathsat5j/compileFor<PLATFORM>.sh`).
Then execute the following command in the JavaSMT directory,
where `$MATHSAT_PATH_<ARCH>` is the paths to the corresponding MathSAT root directory,
and `$MATHSAT_VERSION` is the version number of MathSAT (all-in-one command, runtime is about 10s):
```bash
ant publish-mathsat \
    -Dmathsat-linux-x64.path=$MATHSAT_PATH_LINUX_X64 \
    -Dgmp-linux-x64.path=$GMP_PATH_LINUX_X64 \
    -Dmathsat-windows-x64.path=$MATHSAT_PATH_WINDOWS_X64 \
    -Dgmp-windows-x64.path=$GMP_PATH_WINDOWS_X64 \
    -Djdk-windows-x64.path=$JDK_PATH_WINDOWS_X64 \
    -Dmathsat-linux-arm64.path=$MATHSAT_PATH_LINUX_ARM64 \
    -Dgmp-linux-arm64.path=$GMP_PATH_LINUX_ARM64 \
    -Djdk-linux-arm64.path=$JDK_PATH_LINUX_ARM64 \
    -Dmathsat.version=$MATHSAT_VERSION
```
Example:
```bash
ant publish-mathsat \
     -Dmathsat-linux-x64.path=/workspace/solvers/mathsat/mathsat-5.6.12-linux-x86_64 \
     -Dgmp-linux-x64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-x64 \
     -Dmathsat-windows-x64.path=/workspace/solvers/mathsat/mathsat-5.6.12-win64 \
     -Djdk-windows-x64.path=/workspace/solvers/jdk/openjdk-17.0.2_windows-x64_bin/jdk-17.0.2 \
     -Dgmp-windows-x64.path=/workspace/solvers/gmp/gmp-6.3.0-win-x64 \
     -Dmathsat-linux-arm64.path=/workspace/solvers/mathsat/mathsat-5.6.12-linux-aarch64 \
     -Dgmp-linux-arm64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-arm64 \
     -Djdk-linux-arm64.path=/workspace/solvers/jdk/openjdk-17.0.2_linux-aarch64_bin/jdk-17.0.2 \
     -Dmathsat.version=5.6.12
```
Finally, follow the instructions shown in the message at the end.

A similar procedure applies to [OptiMathSAT](http://optimathsat.disi.unitn.it/) solver,
except that Windows is not yet supported and the publishing command is simpler:
```bash
ant publish-optimathsat -Dmathsat.path=$OPTIMATHSAT_PATH -Dgmp.path=$GMP_PATH -Dmathsat.version=$OPTIMATHSAT_VERSION
```
Example:
```bash
ant publish-optimathsat \
    -Dmathsat.path=/workspace/solvers/optimathsat/optimathsat-1.7.3-linux-64-bit \
    -Dgmp.path=/workspace/solvers/gmp/gmp-6.3.0-linux-x64 \
    -Dmathsat.version=1.7.3-sosy0
```


### Publishing Yices2

Yices2 consists of two components: the solver binary and the Java components in JavaSMT.
The Java components were split from the rest of JavaSMT because of the GPL.

#### 1. Publishing the solver binary for Yices2

We expect one of the Ubuntu docker images to be used for building Yices2. While it's possible to
build the backend without the container, our build script relies on a preinstalled
dependency that is already included when using the docker image. Without it, some paths
would have to be changed, and the user would have to provide their own version of the dependency

#### 1. Build the Yices binaries

We provide a build script for Yices:
```shell
ant publish-yices2 -Dyices2.version=2.8.0-prerelease
```

The script will fetch all dependencies, download and compile Yices, and then build the JNI bindings
that are needed to use the solver from Java

We provide additional `ant` targets for a more fine-grained build:

* `ant build-yices2-java` will build all binaries, but not publish them
* `ant clean-yices2-java` will undo the last build step and delete the JNI bindings
* `ant clean-yices2` will undo the last two build step and delete the Yices binaries and the JNI
  bindings

Changes can then be made to the downloaded source in `downloads` before publishing the binaries
with `ant publish-yices2`. For instance, we could switch to a different branch for Yices:

``` shell
ant build-yices2-java
ant clean-yices2
cd downloads/yices2
git checkout my-branch
cd ../..
ant publish-yices2 -Dyices2.version=2.8.0-prerelease
```

It's also possible to only download the dependencies:

* `ant download-cudd`
* `ant download-poly`
* `ant download-yices2`
* `ant download-yices2-java`

Changes can then be made to the downloaded source before publishing. Compared to the first
method, this avoids the needless initial build

#### 2. Build the JavaSMT backend

In `solvers_ivy_conf/ivy_javasmt_yices2.xml` update the version of the `javasmt-solver-yices2`
dependency:

```xml
<dependency org="org.sosy_lab" name="javasmt-solver-yices2" rev="2.8.0-prerelease" .../>
```

Then, in `lib/ivy.xml` start looking for the following section:

```xml
<!-- additional JavaSMT components with Solver Binaries -->
<dependency org="org.sosy_lab" name="javasmt-yices2" rev="6.0.0-141-g04134287c" conf="runtime-yices2->runtime; contrib->sources,javadoc"/>        
```

Remove the dependency and replace it with a dependency on the solvers:

```xml
<dependency org="org.sosy_lab" name="javasmt-solver-yices2" rev="2.8.0-prerelease" conf="runtime-yices2->solver-yices2; contrib->sources,javadoc"/>
<dependency org="org.sosy_lab" name="javasmt-solver-yices2" rev="2.8.0-prerelease" conf="runtime->solver-yices2; contrib->sources,javadoc"/>
```

Then publish the Yices components of JavaSMT:
```shell
ant publish-artifacts-yices2
```

Finally, return the dependency in `ivy.xml` to its original form, but with the version updated:

```xml
<dependency org="org.sosy_lab" name="javasmt-yices2" rev="yices2.8-prerelease" conf="runtime-yices2->runtime; contrib->sources,javadoc"/>
```

Optionally, you may now publish a new version of JavaSMT:
```shell
ant publish -Dversion=yices-prerelease
```

#### 3. Publish the packages

Test the new version, then publish it to svn:
```shell
# Publish Yices solver binaries
svn add repository/org.sosy_lab/javasmt-solver-yices2/*-2.8.0-prerelease* repository/org.sosy_lab/javasmt-solver-yices2/*/*-2.8.0-prerelease*
svn ci repository/org.sosy_lab/javasmt-solver-yices2 -m"publish version 2.8.0-prerelease of Yices Solver"

# Publish Yices JavaSMT component
svn add repository/org.sosy_lab/javasmt-yices2/*-yices2.8-prerelease* repository/org.sosy_lab/javasmt-yices2/*/*-yices2.8-prerelease*
svn ci repository/org.sosy_lab/javasmt-yices2 -m"publish version yices2.8-prerelease of Yices Solver"

# (Optional) Publish JavaSMT
svn add *-yices-prerelease*
svn ci -m"publish version yices-prerelease of JavaSMT Solver Library"
```

[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
