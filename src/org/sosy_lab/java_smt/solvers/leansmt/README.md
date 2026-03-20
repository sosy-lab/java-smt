# LeanSMT Local Setup (JavaSMT)

LeanSMT upstream: <https://github.com/ufmg-smite/lean-smt>

## Linux x64 Setup

### 1. Install system dependencies

```bash
sudo apt-get install -y git curl unzip
sudo apt-get install -y build-essential gcc g++
sudo apt-get install -y openjdk-17-jdk-headless ant
sudo apt-get install -y swig patchelf ripgrep
```

### 2. Install the Lean toolchain

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

### 3. Clone JavaSMT and LeanSMT

```bash
git clone https://github.com/sosy-lab/java-smt.git java-smt
git clone https://github.com/ufmg-smite/lean-smt.git
cd java-smt
```

### 4. Build and package the LeanSMT runtime

```bash
export PATH="$HOME/.elan/bin:$PATH"
build/build-publish-solvers/build-leansmt-runtime-from-source.sh /absolute/path/to/lean-smt
```

This populates `lib/native/x86_64-linux/` with the packaged LeanSMT runtime, including:

- `libleansmt_jni.so`
- `libleansmt_jni.real.so`
- `libSmtJNI.so`
- `libSmt.so`
- `libAuto.so`
- `libQq.so`
- `libcvc5.so`
- `libleanshared.so`
- `cvc5`

### 5. Verify the runtime

```bash
./lib/native/x86_64-linux/cvc5 --version
ldd ./lib/native/x86_64-linux/libleansmt_jni.real.so
```

`ldd` should resolve the LeanSMT dependencies from `lib/native/x86_64-linux/`.

### 6. Run LeanSMT tests

```bash
ant -q build-project
```

LeanSMT-specific backend tests:

```bash
ant unit-tests-leansmt
```

Normal JavaSMT shared tests with LeanSMT only:

```bash
ant -Dtest.solver=LEANSMT tests
```

To run the full JavaSMT suite for all solvers, use:

```bash
ant tests
```

## Refreshing the packaged runtime

If the LeanSMT runtime has already been built in another checkout, repackage it with:

```bash
build/build-publish-solvers/package-leansmt-runtime.sh /absolute/path/to/runtime-source
```

## Use LeanSMT in JavaSMT

In code, select `Solvers.LEANSMT`.

Minimal example file:
`src/org/sosy_lab/java_smt/example/LeanSmtBasicExample.java`

## Current limitations

- Platform/runtime: Linux x64 only.
- `ubv_to_int` and `sbv_to_int` are not supported.
- Floating points, arrays, strings/regex, interpolation, and optimization are not supported.
- Do not use one LeanSMT context or prover concurrently from multiple threads.

## Related release docs

- Ivy release flow: `doc/Developers-How-to-Release-into-Ivy.md`
- Maven staging flow: `doc/Developers-How-to-Release-into-Maven.md`
