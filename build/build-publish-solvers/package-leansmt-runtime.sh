#!/usr/bin/env bash
set -euo pipefail

# Package LeanSMT runtime artifacts into java-smt, so runtime execution does not
# depend on a sibling ../lean-smt checkout.
#
# Usage:
#   ./build/build-publish-solvers/package-leansmt-runtime.sh /absolute/path/to/lean-smt
#
# Example:
#   ./build/build-publish-solvers/package-leansmt-runtime.sh /home/julius/uni-projects/lean-smt

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /absolute/path/to/lean-smt" >&2
  exit 1
fi

LEAN_SMT_DIR="$1"
JAVA_SMT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
TARGET_DIR="$JAVA_SMT_DIR/lib/native/x86_64-linux/leansmt-runtime"
NATIVE_DIR="$JAVA_SMT_DIR/lib/native/x86_64-linux"
POINTER_FILE="$JAVA_SMT_DIR/lib/native/x86_64-linux/libleansmt_jni.so"
REAL_JNI_FILE="$NATIVE_DIR/libleansmt_jni.real.so"

require_file() {
  local path="$1"
  if [[ ! -f "$path" ]]; then
    echo "Missing required file: $path" >&2
    exit 1
  fi
}

require_file "$LEAN_SMT_DIR/build/libleansmt_jni.so"
require_file "$LEAN_SMT_DIR/.lake/build/lib/libSmtJNI.so"
require_file "$LEAN_SMT_DIR/.lake/build/lib/libSmt.so"
require_file "$LEAN_SMT_DIR/.lake/packages/auto/.lake/build/lib/libAuto.so"
require_file "$LEAN_SMT_DIR/.lake/packages/Qq/.lake/build/lib/libQq.so"
require_file "$LEAN_SMT_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5.so"
require_file "$HOME/.elan/toolchains/leanprover--lean4---v4.26.0/lib/lean/libleanshared.so"

mkdir -p "$TARGET_DIR"
cp -f "$LEAN_SMT_DIR/build/libleansmt_jni.so" "$TARGET_DIR/libleansmt_jni.so"
cp -f "$LEAN_SMT_DIR/.lake/build/lib/libSmtJNI.so" "$TARGET_DIR/libSmtJNI.so"
cp -f "$LEAN_SMT_DIR/.lake/build/lib/libSmt.so" "$TARGET_DIR/libSmt.so"
cp -f "$LEAN_SMT_DIR/.lake/packages/auto/.lake/build/lib/libAuto.so" "$TARGET_DIR/libAuto.so"
cp -f "$LEAN_SMT_DIR/.lake/packages/Qq/.lake/build/lib/libQq.so" "$TARGET_DIR/libQq.so"
cp -f "$LEAN_SMT_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5.so" "$TARGET_DIR/libcvc5.so"
cp -f "$HOME/.elan/toolchains/leanprover--lean4---v4.26.0/lib/lean/libleanshared.so" "$TARGET_DIR/libleanshared.so"

# Mirror runtime libs into the standard JavaSMT native lookup directory so
# dependency preloading can use simple library names.
cp -f "$TARGET_DIR/libSmtJNI.so" "$NATIVE_DIR/libSmtJNI.so"
cp -f "$TARGET_DIR/libSmt.so" "$NATIVE_DIR/libSmt.so"
cp -f "$TARGET_DIR/libAuto.so" "$NATIVE_DIR/libAuto.so"
cp -f "$TARGET_DIR/libQq.so" "$NATIVE_DIR/libQq.so"
cp -f "$TARGET_DIR/libcvc5.so" "$NATIVE_DIR/libcvc5.so"
cp -f "$TARGET_DIR/libleanshared.so" "$NATIVE_DIR/libleanshared.so"
cp -f "$TARGET_DIR/libleansmt_jni.so" "$REAL_JNI_FILE"

# Use a local symlink for the JNI entrypoint to match how several native
# artifacts are wired in this repository.
if [[ -L "$POINTER_FILE" || -f "$POINTER_FILE" ]]; then
  rm -f "$POINTER_FILE"
fi
ln -s "libleansmt_jni.real.so" "$POINTER_FILE"

echo "Packaged LeanSMT runtime into: $TARGET_DIR"
echo "Updated JNI loader entry: $POINTER_FILE"
