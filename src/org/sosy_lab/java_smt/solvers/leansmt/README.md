# LeanSMT Local Setup (JavaSMT)

This README is for running JavaSMT with LeanSMT locally.

LeanSMT upstream: https://github.com/ufmg-smite/lean-smt

## What you need

- JavaSMT checkout
- LeanSMT checkout
- Lean toolchain (elan/lake)
- cvc5 executable available on PATH

## Quickstart (copy/paste)

1. Build LeanSMT

cd /absolute/path/to/lean-smt
lake build

2. Package LeanSMT runtime into JavaSMT

cd /absolute/path/to/java-smt
./build/build-publish-solvers/package-leansmt-runtime.sh /absolute/path/to/lean-smt

3. Verify cvc5 is available

which cvc5
cvc5 --version

4. Build JavaSMT and run LeanSMT tests

ant -q build-project
ant unit-tests-leansmt

## Use LeanSMT in JavaSMT

In code, select Solvers.LEANSMT.

Minimal example file:
src/org/sosy_lab/java_smt/example/LeanSmtBasicExample.java

## Backend notes

- Platform/runtime: packaged for Linux x64.
- External executable: LeanSMT needs cvc5 available.
- Supported: booleans, integers, rationals, bitvectors, UF, SAT/UNSAT, assumptions,
  unsat cores, model generation/evaluation, SMT-LIB parse/dump subset.
- Not supported: floating points, arrays, strings/regex, interpolation, optimization, proofs.
- Threading: do not use one context/prover concurrently from multiple threads.

## Related release docs

- Ivy release flow: doc/Developers-How-to-Release-into-Ivy.md
- Maven staging flow: doc/Developers-How-to-Release-into-Maven.md

