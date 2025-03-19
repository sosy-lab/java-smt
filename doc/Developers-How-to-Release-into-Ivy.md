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

- ant install -Dorganisation=io.github.uuverifiers -Dmodule=princess_2.13 -Drevision=????-??-??
- ant install -Dorganisation=de.uni-freiburg.informatik.ultimate -Dmodule=smtinterpol -Drevision=?.?-???-g???????

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
Java sources and JavaDoc for the bindings, but do no compile any native library.
This only depends on a Python3 environment and Java 17 or later.
For simple usage, we provide a Docker definition/environment under `/docker`, in which the following command can be run.

In the unpacked sources directory, prepare Java sources via `python3 scripts/mk_make.py --java`.
Then execute the following command in the JavaSMT directory,
where `$Z3_DIR` is the path of the sources directory and `$Z3_VERSION` is the version number:
```
ant publish-z3 -Dz3.path=$Z3_DIR -Dz3.version=$Z3_VERSION
```
Example:
```
ant publish-z3 -Dz3.path=/workspace/solvers/z3/z3-z3-4.13.3 -Dz3.version=4.13.3
```
Finally, follow the instructions shown in the message at the end.


#### Optional (from source for Linux target with older GLIBC)
This step is for the following use case:
Newer releases of Z3 depend on newer versions of GLIBC (>=v2.35),
so we want to compile the Linux release on our own and then combine it with the provided libraries for Windows and MacOS.
We follow the steps from above, download and unpack the given zip archives for all platforms, except the Linux release (where the GLIBC is too new).
For simple usage, we provide a Docker definition/environment under `/docker` (based on Ubuntu 18.04 with GLIBC 2.27),
in which the following build command can be run in the unpacked source directory:
```
python3 scripts/mk_make.py --java && cd build && make -j 2
```
Afterwards copy the native libraries for Linux (`libz3.so` and `libz3java.so`) from the directory 
`./build` into `./bin` (if needed, adjust the directory to match the x64 or arm64 path for Linux).
Then perform as written above with adding the additional pre-compiled binaries for other operating systems,
and publish the directory `./bin` with an ant command like the one from above:
```
ant publish-z3 -Dz3.path=$Z3_DIR -Dz3.version=$Z3_VERSION-glibc_2.27
```


#### Optional (from source for Linux target) (Info: this step is outdated and no longer used for releases of JavaSMT)
To publish Z3 from source, [download it](https://github.com/Z3Prover/z3) and build
it with the following command in its directory on a 64bit Ubuntu 16.04 system:
```
./configure --staticlib --java --git-describe && cd build && make -j 2
```
(Note that additional binaries for other operating systems need to be provided, too.
This step is currently not fully tested from our side.)
Then execute the following command in the JavaSMT directory, where `$Z3_DIR` is the absolute path of the Z3 directory:
```
ant publish-z3 -Dz3.path=$Z3_DIR/build
```
Finally follow the instructions shown in the message at the end.


### Publishing CVC5 (previously CVC4)

We prefer to compile our own CVC5 binaries and Java bindings.
For simple usage, we provide a Docker definition/environment under `/docker`,
in which the following command can be run.

To publish CVC5, checkout the [CVC5 repository](https://github.com/cvc5/cvc5).
Then execute the following command in the JavaSMT directory,
where `$CVC5_DIR` is the path to the CVC5 directory and `$CVC5_VERSION` is the version number:
```
ant publish-cvc5 -Dcvc5.path=$CVC5_DIR -Dcvc5.customRev=$CVC5_VERSION
```
Example:
```
ant publish-cvc5 -Dcvc5.path=../CVC5 -Dcvc5.customRev=1.0.1
```
During the build process, our script automatically appends the git-revision after the version.
Finally, follow the instructions shown in the message at the end.


### Publishing OpenSMT

We prefer to use our own OpenSMT binaries and SWIG-based Java bindings.
We prefer to build directly on Ubuntu 22.04, where CMake, SWIG, and GCC are sufficiently up-to-date.
For simple usage, we provide a Docker definition/environment under `/docker`,
in which the following command can be run.

Please provide GMP from http://gmplib.org/ in version 6.3.0 (version 6.2.1 also works) and build GMP:
- For linux-x64 in directory $GMP_DIR_LINUX_X64:
  ```
  ./configure --enable-cxx --with-pic --disable-shared --enable-static --enable-fat
  make -j4
  ```
- For linux-arm64 in directory $GMP_DIR_LINUX_ARM64:
  ```
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
```
ant publish-opensmt \
    -Dopensmt.path=$OPENSMT_DIR \
    -Dopensmt.customRev=$VERSION \
    -Dgmp-linux-x64.path=$GMP_DIR_LINUX_X64 \
    -Dgmp-linux-arm64.path=$GMP_DIR_LINUX_ARM64 \
    -Djdk-linux-arm64.path=$JDK_DIR_LINUX_ARM64
```
Example:
```
ant publish-opensmt \
    -Dopensmt.path=/workspace/solvers/opensmt/opensmt \
    -Dopensmt.customRev=2.8.0-sosy0 \
    -Dgmp-linux-x64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-x64 \
    -Dgmp-linux-arm64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-arm64 \
    -Djdk-linux-arm64.path=/workspace/solvers/jdk/openjdk-17.0.2_linux-aarch64_bin/jdk-17.0.2
```
The build scripts for OpenSMT ... :
- run for about 20 minutes (we build everything from scratch, two times).
- download Google-based test components (requires internet access).
- append the git revision of Bitwuzla.
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
```
CC=gcc-7 ant publish-boolector -Dboolector.path=$BTOR_DIR -Dboolector.customRev=$BTOR_VERSION
```
Example:
```
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
in which the following command can be run.

To publish Bitwuzla, checkout the [Bitwuzla repository](https://github.com/bitwuzla/bitwuzla).
Then execute the following command in the JavaSMT directory:
```
ant publish-bitwuzla \
     -Dbitwuzla.path=$BITWUZLA_DIR \
     -Dbitwuzla.customRev=$VERSION \
     -Dbitwuzla.rebuildWrapper=false \
     -Djdk-windows.path=$JDK_DIR_WINDOWS \
     -Djdk-linux-arm64.path=$JDK_DIR_LINUX_ARM64
```
Example:
```
ant publish-bitwuzla \
    -Dbitwuzla.path=/workspace/solvers/bitwuzla/bitwuzla/ \
    -Dbitwuzla.customRev=0.7.0-13 \
    -Dbitwuzla.rebuildWrapper=false \
    -Djdk-windows-x64.path=/workspace/solvers/jdk/openjdk-17.0.2_windows-x64_bin/jdk-17.0.2/ \
    -Djdk-linux-arm64.path=/workspace/solvers/jdk/openjdk-17.0.2_linux-aarch64_bin/jdk-17.0.2/
```
The build scripts for Bitwuzla ... :
- run for about 10 minutes (we build everything from scratch, three times).
- download and build necessary dependencies like GMP automatically. 
- append the git revision of Bitwuzla.
- produce two Linux (x64 and arm64) libraries and one Windows (x64) library, and publish them.

Finally, follow the instructions shown in the message at the end of the command.
The instructions for publication via SVN into the Ivy repository are not intended to be executed in the Docker environment,
but in the normal system environment, where some testing can be applied by the developer before the commit.


### Publishing (Opti)-MathSAT5

We publish MathSAT for Linux (x64 and arm64) and Windows (x64) systems at once.
The build process can fully be done on a Linux system, 
and requires several dependencies, such as gcc, x86_64-w64-mingw32-gcc, and aarch64-linux-gnu-gcc.
We prefer to use the Docker container based on Ubuntu 22.04 (better use Ubuntu 18.04 for older GLIBC!)
for compiling the dependencies and assembling the libraries.

First, [download the (reentrant!) Linux and Windows64 binary release](http://mathsat.fbk.eu/download.html) in the same version, unpack them.
Then provide the necessary dependencies (GMP/JDK for Linux (x64 and arm64) and GMP/JDK for Windows (x64))
as described in the compilation scripts (see `lib/native/source/libmathsat5j/compileFor<PLATFORM>.sh`).
Then execute the following command in the JavaSMT directory,
where `$MATHSAT_PATH_<ARCH>` is the paths to the corresponding MathSAT root directory,
and `$MATHSAT_VERSION` is the version number of MathSAT (all-in-one command, runtime is about 10s):
```
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
```
ant publish-mathsat \
     -Dmathsat-linux-x64.path=/workspace/solvers/mathsat/mathsat-5.6.11-linux-x86_64-reentrant \
     -Dgmp-linux-x64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-x64 \
     -Dmathsat-windows-x64.path=/workspace/solvers/mathsat/mathsat-5.6.11-win64-msvc \
     -Djdk-windows-x64.path=/workspace/solvers/jdk/openjdk-17.0.2_windows-x64_bin/jdk-17.0.2 \
     -Dgmp-windows-x64.path=/workspace/solvers/gmp/gmp-6.3.0-win-x64 \
     -Dmathsat-linux-arm64.path=/workspace/solvers/mathsat/mathsat-5.6.11-linux-aarch64-reentrant \
     -Dgmp-linux-arm64.path=/workspace/solvers/gmp/gmp-6.3.0-linux-arm64 \
     -Djdk-linux-arm64.path=/workspace/solvers/jdk/openjdk-17.0.2_linux-aarch64_bin/jdk-17.0.2 \
     -Dmathsat.version=5.6.11
```
Finally, follow the instructions shown in the message at the end.

A similar procedure applies to [OptiMathSAT](http://optimathsat.disi.unitn.it/) solver,
except that Windows is not yet supported and the publishing command is simpler:
```
ant publish-optimathsat -Dmathsat.path=$OPTIMATHSAT_PATH -Dgmp.path=$GMP_PATH -Dmathsat.version=$OPTIMATHSAT_VERSION
```


### Publishing Yices2

Yices2 consists of two components: the solver binary and the Java components in JavaSMT.
The Java components were splitt from the rest of JavaSMT because of the GPL.

#### Publishing the solver binary for Yices2

Prepare gperf and gmp (required for our own static binary):
```
wget http://ftp.gnu.org/pub/gnu/gperf/gperf-3.1.tar.gz && tar -zxvf gperf-3.1.tar.gz && cd gperf-3.1 && ./configure --enable-cxx --with-pic --disable-shared --enable-fat && make
wget https://gmplib.org/download/gmp/gmp-6.2.0.tar.xz && tar -xvf gmp-6.2.0.tar.xz && cd gmp-6.2.0 && ./configure --enable-cxx --with-pic --disable-shared --enable-fat && make
```

Download and build Yices2 from source:
```
git clone git@github.com:SRI-CSL/yices2.git && cd yices2 && autoconf && ./configure --with-pic-gmp=../gmp-6.2.0/.libs/libgmp.a && make
```

Get the version of Yices2:
```
git describe --tags
```

Publish the solver binary from within JavaSMT (adjust all paths to your system!):
```
ant publish-yices2 -Dyices2.path=../solvers/yices2 -Dgmp.path=../solvers/gmp-6.2.0 -Dgperf.path=../solvers/gperf-3.1 -Dyices2.version=2.6.2-89-g0f77dc4b
```

Afterwards you need to update the version number in `solvers_ivy_conf/ivy_javasmt_yices2.xml` and publish new Java components for Yices2.

#### Publish the Java components for Yices2

Info: There is a small cyclic dependency: JavaSMT itself depends on the Java components of Yices2.

As long as no API was changed and compilation succeeds, simply execute `ant publish-artifacts-yices2`.

If the API was changed, we need to break the dependency cycle for the publication and revert this later:
edit `lib/ivy.xml` and replace the dependency towards `javasmt-yices2` with the dependency towards `javasmt-solver-yices2`
(the line can be copied from `solvers_ivy_conf/ivy_javasmt_yices2.xml`).
Then run `ant publish-artifacts-yices2`.
We still need to figure out how to avoid the warning about a dirty repository in that case, e.g. by a temporary commit.

[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
