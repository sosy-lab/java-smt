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

To publish Z3, download the **Ubuntu 16.04**, **Windows**, and **OSX** binary
and the sources (for JavaDoc) for the [latest release](https://github.com/Z3Prover/z3/releases) and unzip them.
In the unpacked sources directory, prepare Java sources via `python scripts/mk_make.py --java`.
For simpler handling, we then copy the files from the three `bin` directories together into one directory,
and include the sources (we can keep the internal structure of each directory, just copy them above each other).
Then execute the following command in the JavaSMT directory,
where `$Z3_DIR` is the absolute path of the unpacked Z3 directory
and `$Z3_VERSION` is the version number:
```
ant publish-z3 -Dz3.path=$Z3_DIR/bin -Dz3.version=$Z3_VERSION
```
Finally follow the instructions shown in the message at the end.

#### Optional
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
Boolector's dependencies, mainly Minisat, requires GCC version 7 and does not yet compile with newer compilers.
We prefer to directly build directly on Ubuntu 18.04, where gcc-7 is the default compiler.
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
Our build script will automatically append the git-revision of Boolector, if available.

Finally follow the instructions shown in the message at the end.
The instructions for publication via SVN into the Ivy repository are not intended to be executed in the Docker environment,
but in the normal system environment, where some testing can be applied by the developer before the commit.


### Publishing (Opti)-MathSAT5

We publish MathSAT for both Linux and Windows systems at once.
The build process can fully be done on a Linux system.

For publishing MathSAT5, you need to use a Linux machine with at least GCC 7.5.0 and x86_64-w64-mingw32-gcc 7.3.
First, [download the (reentrant!) Linux and Windows64 binary release](http://mathsat.fbk.eu/download.html) in the same version, unpack them,
then provide the necessary dependencies (GMP for Linux and MPIR/JDK for Windows) as described in the compilation scripts.
(see `lib/native/source/libmathsat5j/`), and then execute the following command in the JavaSMT directory,
where `$MATHSAT_PATH_LINUX` and `$MATHSAT_PATH_WINDOWS` are the paths to the MathSAT root directory,
and `$MATHSAT_VERSION` is the version number of MathSAT (all-in-one, runtime: less than 5s):
```
  ant publish-mathsat \
      -Dmathsat.path=$MATHSAT_PATH_LINUX \
      -Dgmp.path=$GMP_PATH \
      -Dmathsat-windows.path=$MATHSAT_PATH_WINDOWS \
      -Dmpir-windows.path=$MPIR_PATH \
      -Djdk-windows.path=$JDK_11_PATH \
      -Dmathsat.version=$MATHSAT_VERSION
```
Concrete example (`$WD` is a working directory where all dependencies are located):
```
  ant publish-mathsat \
      -Dmathsat.path=$WD/mathsat-5.6.4-linux-x86_64-reentrant \
      -Dgmp.path=$WD/gmp-6.1.2 \
      -Dmathsat-windows.path=$WD/mathsat-5.6.4-win64-msvc \
      -Dmpir-windows.path=$WD/mpir-2.7.2-win \
      -Djdk-windows.path=$WD/jdk-11 \
      -Dmathsat.version=5.6.4-debug
```
Finally follow the instructions shown in the message at the end.

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
ant publish-yices2 -Dyices2.path=../solver/yices2 -Dgmp.path=../solver/gmp-6.2.0 -Dgperf.path=../solver/gperf-3.1 -Dyices2.version=2.6.2-89-g0f77dc4b
```

Afterwards you need to update the version number in `solvers_ivy_conf/ivy_javasmt_yices2.xml` and publish new Java components for Yices2.

#### Publish the Java components for Yices2

Info: There is a small cyclic dependency: JavaSMT itself depends on the Java components of Yices2.

As long as no API was changed and compilation suceeds, simply execute `ant publish-artifacts-yices2`.

If the API was changed, we need to break the dependency cycle for the publication and revert this later:
edit `lib/ivy.xml` and replace the dependency towards `javasmt-yices2` with the dependency towards `javasmt-solver-yices2`
(the line can be copied from `solvers_ivy_conf/ivy_javasmt_yices2.xml`).
Then run `ant publish-artifact-yices2`.
We still need to figure out how to avoid the warning about a dirty repository in that case, e.g. by a temporary commit.

[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
