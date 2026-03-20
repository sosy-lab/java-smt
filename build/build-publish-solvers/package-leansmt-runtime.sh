#!/usr/bin/env bash
set -euo pipefail

# Package LeanSMT runtime artifacts into java-smt, so runtime execution does not
# depend on a sibling ../lean-smt checkout.
#
# Usage:
#   ./build/build-publish-solvers/package-leansmt-runtime.sh /absolute/path/to/runtime-source
#
# Example:
#   ./build/build-publish-solvers/package-leansmt-runtime.sh /home/julius/uni-projects/java-smt-runtime-bundle
#
# Supported runtime sources:
# - a JavaSMT checkout or runtime bundle that already contains
#   lib/native/x86_64-linux/libleansmt_jni.so and its transitive LeanSMT libs
# - a dedicated runtime directory with those .so files directly inside it
# - a JavaSMT-specific LeanSMT integration checkout that already contains
#   build/libleansmt_jni.so plus the Lean-generated .so files
#
# A plain upstream https://github.com/ufmg-smite/lean-smt checkout built only with
# `lake build` is currently not enough on its own, because it does not provide the
# JavaSMT JNI wrapper library (`libleansmt_jni.so`) expected by this repository.

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /absolute/path/to/runtime-source" >&2
  exit 1
fi

SOURCE_DIR="$(cd "$1" && pwd)"
JAVA_SMT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
TARGET_DIR="$JAVA_SMT_DIR/lib/native/x86_64-linux/leansmt-runtime"
NATIVE_DIR="$JAVA_SMT_DIR/lib/native/x86_64-linux"
POINTER_FILE="$JAVA_SMT_DIR/lib/native/x86_64-linux/libleansmt_jni.so"
REAL_JNI_FILE="$NATIVE_DIR/libleansmt_jni.real.so"
DIRECT_BUNDLE_DIR=""
CHECKOUT_DIR=""

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "Missing required command: $cmd" >&2
    exit 1
  fi
}

require_file() {
  local path="$1"
  if [[ ! -f "$path" ]]; then
    echo "Missing required file: $path" >&2
    exit 1
  fi
}

copy_runtime_file() {
  local src="$1"
  local name="$2"
  cp -f "$src" "$TARGET_DIR/$name"
  cp -f "$src" "$NATIVE_DIR/$name"
}

ensure_runtime_alias() {
  local alias_name="$1"
  local target_name="$2"
  local dir

  if [[ "$alias_name" == "$target_name" ]]; then
    return 0
  fi

  for dir in "$TARGET_DIR" "$NATIVE_DIR"; do
    if [[ -e "$dir/$alias_name" || -L "$dir/$alias_name" ]]; then
      rm -f "$dir/$alias_name"
    fi
    ln -s "$target_name" "$dir/$alias_name"
  done
}

find_first_existing() {
  for candidate in "$@"; do
    if [[ -n "$candidate" && -f "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

find_first_executable() {
  for candidate in "$@"; do
    if [[ -n "$candidate" && -x "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

detect_lean_sysroot() {
  local checkout_dir="$1"
  (cd "$checkout_dir" && lake env lean --print-prefix)
}

require_cmd patchelf

if [[ -f "$SOURCE_DIR/lib/native/x86_64-linux/libleansmt_jni.so" ]]; then
  DIRECT_BUNDLE_DIR="$SOURCE_DIR/lib/native/x86_64-linux"
elif [[ -f "$SOURCE_DIR/libleansmt_jni.so" ]]; then
  DIRECT_BUNDLE_DIR="$SOURCE_DIR"
elif [[ -f "$SOURCE_DIR/build/libleansmt_jni.so" ]]; then
  CHECKOUT_DIR="$SOURCE_DIR"
else
  cat >&2 <<EOF
Could not find a LeanSMT runtime source under: $SOURCE_DIR

Expected one of:
- lib/native/x86_64-linux/libleansmt_jni.so
- libleansmt_jni.so
- build/libleansmt_jni.so

Note: a plain upstream LeanSMT checkout built only with 'lake build' is not
enough for JavaSMT today, because JavaSMT also requires the JNI wrapper library
'libleansmt_jni.so'.
EOF
  exit 1
fi

mkdir -p "$TARGET_DIR" "$NATIVE_DIR"

if [[ -n "$DIRECT_BUNDLE_DIR" ]]; then
  require_file "$DIRECT_BUNDLE_DIR/libleansmt_jni.so"
  require_file "$DIRECT_BUNDLE_DIR/libSmtJNI.so"
  require_file "$DIRECT_BUNDLE_DIR/libSmt.so"
  require_file "$DIRECT_BUNDLE_DIR/libAuto.so"
  require_file "$DIRECT_BUNDLE_DIR/libQq.so"
  require_file "$DIRECT_BUNDLE_DIR/libcvc5.so"
  require_file "$DIRECT_BUNDLE_DIR/libleanshared.so"

  copy_runtime_file "$DIRECT_BUNDLE_DIR/libleansmt_jni.so" "libleansmt_jni.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libSmtJNI.so" "libSmtJNI.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libSmt.so" "libSmt.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libAuto.so" "libAuto.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libQq.so" "libQq.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libcvc5.so" "libcvc5.so"
  copy_runtime_file "$DIRECT_BUNDLE_DIR/libleanshared.so" "libleanshared.so"

  CVC5_SOURCE="$(find_first_executable \
    "$DIRECT_BUNDLE_DIR/leansmt-runtime/bin/cvc5" \
    "$DIRECT_BUNDLE_DIR/leansmt-runtime/cvc5" \
    "$DIRECT_BUNDLE_DIR/cvc5" \
    "$(command -v cvc5 || true)" || true)"
else
  require_file "$CHECKOUT_DIR/build/libleansmt_jni.so"
  require_cmd lake

  SMT_JNI_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/build/lib/libSmtJNI.so" \
    "$CHECKOUT_DIR/.lake/build/lib/libsmt_SmtJNI.so" || true)"
  SMT_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/build/lib/libSmt.so" \
    "$CHECKOUT_DIR/.lake/build/lib/libsmt_Smt.so" || true)"
  AUTO_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/packages/auto/.lake/build/lib/libAuto.so" \
    "$CHECKOUT_DIR/.lake/packages/auto/.lake/build/lib/libauto_Auto.so" || true)"
  QQ_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/packages/Qq/.lake/build/lib/libQq.so" \
    "$CHECKOUT_DIR/.lake/packages/Qq/.lake/build/lib/libQq_Qq.so" || true)"
  CVC5_LIB_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5.so" \
    "$CHECKOUT_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so" || true)"
  LEAN_SYSROOT="$(detect_lean_sysroot "$CHECKOUT_DIR")"
  LEAN_SHARED_SOURCE="$(find_first_existing \
    "$CHECKOUT_DIR/.lake/packages/lean4/build/lib/lean/libleanshared.so" \
    "$LEAN_SYSROOT/lib/lean/libleanshared.so" || true)"
  require_file "$SMT_JNI_SOURCE"
  require_file "$SMT_SOURCE"
  require_file "$AUTO_SOURCE"
  require_file "$QQ_SOURCE"
  require_file "$CVC5_LIB_SOURCE"
  require_file "$LEAN_SHARED_SOURCE"

  copy_runtime_file "$CHECKOUT_DIR/build/libleansmt_jni.so" "libleansmt_jni.so"
  copy_runtime_file "$SMT_JNI_SOURCE" "libSmtJNI.so"
  copy_runtime_file "$SMT_SOURCE" "libSmt.so"
  copy_runtime_file "$AUTO_SOURCE" "libAuto.so"
  copy_runtime_file "$QQ_SOURCE" "libQq.so"
  copy_runtime_file "$CVC5_LIB_SOURCE" "libcvc5.so"
  copy_runtime_file "$LEAN_SHARED_SOURCE" "libleanshared.so"
  ensure_runtime_alias "$(basename "$SMT_JNI_SOURCE")" "libSmtJNI.so"
  ensure_runtime_alias "$(basename "$SMT_SOURCE")" "libSmt.so"
  ensure_runtime_alias "$(basename "$AUTO_SOURCE")" "libAuto.so"
  ensure_runtime_alias "$(basename "$QQ_SOURCE")" "libQq.so"
  ensure_runtime_alias "$(basename "$CVC5_LIB_SOURCE")" "libcvc5.so"

  CVC5_SOURCE="$(find_first_executable \
    "$CHECKOUT_DIR/.lake/packages/cvc5/.lake/build/bin/cvc5" \
    "$CHECKOUT_DIR/.lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5" \
    "$(find "$CHECKOUT_DIR/.lake/packages/cvc5" -path '*/bin/cvc5' 2>/dev/null | head -n 1)" \
    "$(command -v cvc5 || true)" || true)"
fi

cp -f "$TARGET_DIR/libleansmt_jni.so" "$REAL_JNI_FILE"
patchelf --set-rpath '$ORIGIN' "$REAL_JNI_FILE"

if [[ -n "${CVC5_SOURCE:-}" ]]; then
  mkdir -p "$TARGET_DIR/bin"
  cp -f "$CVC5_SOURCE" "$TARGET_DIR/bin/cvc5"
  cp -f "$CVC5_SOURCE" "$TARGET_DIR/../cvc5"
  cp -f "$CVC5_SOURCE" "$NATIVE_DIR/cvc5"
  chmod +x "$TARGET_DIR/bin/cvc5" "$TARGET_DIR/../cvc5" "$NATIVE_DIR/cvc5"
else
  echo "Warning: no cvc5 executable was found to package." >&2
fi

# Use a local symlink for the JNI entrypoint to match how several native
# artifacts are wired in this repository.
if [[ -L "$POINTER_FILE" || -f "$POINTER_FILE" ]]; then
  rm -f "$POINTER_FILE"
fi
ln -s "libleansmt_jni.real.so" "$POINTER_FILE"

echo "Packaged LeanSMT runtime into: $TARGET_DIR"
echo "Updated JNI loader entry: $POINTER_FILE"
echo "Normalized JNI RUNPATH to: \$ORIGIN"
