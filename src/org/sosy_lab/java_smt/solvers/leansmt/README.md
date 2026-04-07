# LeanSMT Local Setup (JavaSMT)

LeanSMT upstream: <https://github.com/ufmg-smite/lean-smt>

This is the supported local setup for LeanSMT in JavaSMT today:

- build on Linux x64 only
- keep the upstream `lean-smt` checkout immutable
- stage the runtime once in `build/leansmt-staging/x64`
- expose it through symlinks in `lib/native/x86_64-linux`
- keep the original Lean-produced library names (`libsmt_SmtJNI.so`, `libauto_Auto.so`, ...)

If you are working on a macOS laptop, run these steps inside an Ubuntu 24.04 x64 OrbStack VM or
another Linux x64 VM/container. Do not run the runtime build on the macOS host.

## Fresh Ubuntu 24.04 x64 VM

### 1. Install the system packages

```bash
sudo apt-get update
sudo apt-get install -y \
  ant \
  binutils \
  build-essential \
  curl \
  git \
  openjdk-21-jdk-headless \
  ripgrep \
  unzip
```

### 2. Install the Lean toolchain

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

### 3. Clone JavaSMT and the pinned LeanSMT revision

```bash
git clone https://github.com/sosy-lab/java-smt.git
cd java-smt
LEANSMT_REMOTE="$(sed -n 's/^LEANSMT_REMOTE=//p' lib/native/source/libleansmt/lean-smt.lock)"
LEANSMT_COMMIT="$(sed -n 's/^LEANSMT_COMMIT=//p' lib/native/source/libleansmt/lean-smt.lock)"
git clone "$LEANSMT_REMOTE" ../lean-smt
git -C ../lean-smt checkout "$LEANSMT_COMMIT"
```

The pinned LeanSMT revision currently used by JavaSMT is stored in:
`lib/native/source/libleansmt/lean-smt.lock`

### 4. Build the local LeanSMT runtime

```bash
export PATH="$HOME/.elan/bin:$PATH"
./lib/native/source/libleansmt/build-runtime.sh /absolute/path/to/lean-smt
```

This script does not mutate the source checkout. It rebuilds from a throwaway copy in
`build/lean-smt-work`, stages the runtime in `build/leansmt-staging/x64`, and refreshes the
LeanSMT symlinks in `lib/native/x86_64-linux`.

### 5. Verify the staged runtime

Check that the bundled solver executable is present:

```bash
./lib/native/x86_64-linux/cvc5 --version
```

Check that the JNI library keeps only a local runtime search path:

```bash
objdump -p ./build/leansmt-staging/x64/libleansmt_jni.so | egrep 'NEEDED|RUNPATH'
```

The output should mention these LeanSMT dependencies by their original names:

- `libsmt_SmtJNI.so`
- `libsmt_Smt.so`
- `libauto_Auto.so`
- `libQq_Qq.so`
- `libcvc5_cvc5.so`
- `libleanshared.so`

The `RUNPATH` should be exactly `$ORIGIN`.

### 6. Run LeanSMT tests

```bash
ant -q build-project
ant unit-tests-leansmt
ant -Dtest.solver=LEANSMT tests
```

## Notes

- The builder enforces the pinned LeanSMT commit by default. Set `LEANSMT_SKIP_PIN_CHECK=1` only
  for local experiments.
- The local runtime layout is intentionally minimal. It does not rely on `leansmt-runtime/`,
  renamed alias libraries, or host-specific absolute RPATHs.
- JavaSMT loads LeanSMT through the normal native-library loader and the symlink layer in
  `lib/native/x86_64-linux`.

## Use LeanSMT in JavaSMT

In code, select `Solvers.LEANSMT`.

Minimal example file:
`src/org/sosy_lab/java_smt/example/LeanSmtBasicExample.java`

## Current limitations

- Platform/runtime: Linux x64 only.
- The java-smt backend uses lean-smt in one-shot mode. Each satisfiability check rebuilds a fresh
  solver snapshot from the active assertion stack.
- Models come from one-shot SAT snapshots. `evaluate(...)` only queries the original snapshot and
  does not mutate or extend it.
- Assumption solving is not supported.
- Unsat cores are not supported.
- `ubv_to_int`, `sbv_to_int`, and `(_ int_to_bv n)` are supported.
- Symbolic bitvector rotations use java-smt's shared bitvector lowering.
- Floating points, arrays, strings/regex, interpolation, and optimization are not supported.
- Do not use one LeanSMT context or prover concurrently from multiple threads.
