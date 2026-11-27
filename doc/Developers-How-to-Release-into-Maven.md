<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

# Release JavaSMT or Solver Binaries to Maven Central

Please read the hints on release in the [developer documentation](Developers.md) first.

We only release something to Maven after doing an Ivy release.
Our infrastructure is designed to resolve artifacts from our [Ivy repository](https://www.sosy-lab.org/ivy/) and package them for Maven Central.

Make sure that all necessary dependency libraries are already released on Maven Central
before (or shortly after) publishing a new version of JavaSMT.
Dependencies like `SMTInterpol`, `Princess`, and `SoSy-Lab Common` need to be available via Maven in the correct version.
Publish dependencies first (solvers, then `javasmt-yices2`), and `java-smt` last,
because its POM references the exact versions of all solvers.

## Automation vs. Manual Steps

The release process uses the [Sonatype Central Publishing Portal](https://central.sonatype.com/):
1. **Automated Upload:** Use Ant targets to resolve artifacts from Ivy, generate POMs, sign artifacts, and upload a deployment bundle.
2. **Manual Release:** Log in to the portal to review the validated deployment and finalize the release.

## Requirements

### 1. Account
Register at [Sonatype Central](https://central.sonatype.com/) and ensure you have access to the `org.sosy-lab` namespace.

### 2. PGP Key
- You need a GPG key pair (Ed25519, or RSA 2048-bit or higher).
- The build signs with gpg's default key. If you have several secret keys,
  set `default-key <KEY_ID>` in `~/.gnupg/gpg.conf`.
- Your public key **must** be published to a supported keyserver:
  `gpg --keyserver keyserver.ubuntu.com --send-keys <KEY_ID>`
- For the publication process, the passphrase can be provided via `-Dgpg.passphrase=...` or stored in `build.properties`.
  There is no interactive prompt, so ensure the passphrase is accessible to the build process.

### 3. Authentication Token
- Log in to [Sonatype Central](https://central.sonatype.com/), go to **Account**, and **Generate User Token**.
- Add the credentials to your `~/.m2/settings.xml` as follows:

```xml
<settings>
    <servers>
        <server>
            <id>SonatypeCentral</id>
            <username>TOKEN_NAME</username>
            <password>TOKEN_PASSWORD</password>
        </server>
    </servers>
</settings>
```

## Publishing

To publish a component, use the `publish-to-maven-central` Ant target.
This target automatically handles the resolution from Ivy and the bundle creation.
The POM is generated from the published `ivy-<version>.xml` of the component.
Its dependency versions are the declared versions (`revConstraint`) of that file,
not the `rev` values written by `ivy:deliver`, which may stem from a non-runtime configuration.

### Commands

For JavaSMT itself:
```bash
ant publish-to-maven-central -Dpublish.component=java-smt -Dpublish.version=5.0.0
```

For binary solvers or bindings:
```bash
# Example for Z3
ant publish-to-maven-central -Dpublish.component=javasmt-solver-z3 -Dpublish.version=4.15.4

# Example for Yices2 bindings
ant publish-to-maven-central -Dpublish.component=javasmt-yices2 -Dpublish.version=6.0.0-141-g04134287c
```

### Testing and Debugging
- To prepare the bundle without uploading, add `-Dpublish.upload=false`.
  Always do this first and check the generated POM (coordinates, packaging, dependency versions), e.g.:
  `unzip -p dist/maven-central-bundle/<component>-<version>-bundle.zip '*.pom'`
- You can use `scripts/test-maven-central-bundle.sh` to verify the bundle structure locally.
  It contains several hardcoded paths and versions, so adjust it as needed for your case.

## Finalizing Publication

1.  **Review and Publish:**
    - Log in to [Sonatype Central Deployments](https://central.sonatype.com/publishing/deployments).
    - Check that the deployment is validated and contains all expected files.
    - Click **Publish** to start the release process.
      This cannot be undone: once a deployment is in state PUBLISHING, it can no longer be dropped,
      and a released version can never be replaced.
2.  **Wait for Sync:**
    - It usually takes about 15–30 minutes for the artifacts to appear in [Maven Central](https://repo1.maven.org/maven2/org/sosy-lab/).
    - Search results on the Sonatype portal might take longer to update.
