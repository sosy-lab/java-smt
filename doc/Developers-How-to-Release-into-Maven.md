<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Release JavaSMT or Solver Binaries to Maven Central

Please read the hints on release in the [developer documentation](Developers.md) first.

We only release something to Maven after doing an Ivy release.
With our project infrastructure is much simpler to test packages from (local) Ivy repository than from Maven.

Make sure that all necessary dependency libraries are already released on Maven Central,
before (or at least while) publishing a new version of JavaSMT.
Maven does not check for existing or non-existing dependencies automatically.
Dependencies like `SMTIntinterpol`, `Princess`, and `SoSy-Lab Common` need to be available via Maven in the correct version.
A release of `SoSy-Lab Common` can be uploaded to Maven by us, even afterward :-).


## Automation vs. Manual Steps

The release to Maven Central is currently not fully automated due to the bug in the
ANT script provided by Maven Central documentation.
For publishing to Maven Central, we use the [Nexus Repository Manager][].
We first upload files into that repository, and later manually publish them from there.
There is no need to manually change any file for the upload process.


## Requirements

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
        <gpg.executable>gpg</gpg.executable>
        <!-- optional <gpg.passphrase>PASSPHRASE</gpg.passphrase> -->
      </properties>
    </profile>
  </profiles>
  <mirrors>
    <mirror>
      <id>centralhttps</id>
      <mirrorOf>central</mirrorOf>
      <name>Maven central https</name>
      <url>https://repo1.maven.org/maven2/</url>
    </mirror>
  </mirrors>
</settings>
```

If default system settings are not configured for HTTPS,
we get an 501 error when downloading further maven dependencies.
Thus, we add a mirror for HTTPS.

You might need to store `maven-ant-tasks-2.1.3.jar` (or newer version) under `~/.ant/lib/`
to avoid a failure when creating the task `antlib:org.apache.maven.artifact.ant:mvn`.


## Publishing

For publishing JavaSMT itself:
- Execute `ant stage` to upload the local build of JavaSMT into the [Nexus Repository Manager][].
  This is ideally done directly after a release to our [Ivy Repository][].
- Login to the [Nexus Repository Manager][] and freeze (`close`) the entry in the [staging repositories][],
  and inspect the files for correctness and completeness!
- Later `release` your staged bundle.
  After some delay (a few hours) the release is automatically synced to Maven Central.

For publishing binary solvers like Boolector, CVC4, MathSAT5, Yices2, or Z3, the process is similar:
- Execute `ant stage-SOLVER` to upload the currently installed binary solvers into the [Nexus Repository Manager]
  whenever there was an update for the corresponding solver.
  This is ideally done directly after a release of the solver to our [Ivy Repository][].
  For Yices2, we might require the execution of `ant stage-javasmt-yices2` to release the package `javasmt-yices2`.
- Login to the [Nexus Repository Manager][] and freeze (`close`) the entry in the [staging repositories][],
  and inspect the files for correctness and completeness!
- Later `release` your staged bundle.
  After some delay (a few hours) the release is automatically synced to Maven Central.

Additional instructions are available at the official [OSSRH][] page and
the [documentation](http://central.sonatype.org/pages/releasing-the-deployment.html).

[Ivy Repository]: http://www.sosy-lab.org/ivy/org.sosy_lab/
[OSSRH]: http://central.sonatype.org/pages/ossrh-guide.html
[Nexus Repository Manager]: https://oss.sonatype.org/
[staging repositories]: https://oss.sonatype.org/#stagingRepositories
