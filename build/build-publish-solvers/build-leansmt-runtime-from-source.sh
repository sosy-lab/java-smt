#!/usr/bin/env bash
set -euo pipefail

# Rebuild the JavaSMT-compatible LeanSMT runtime from a fresh upstream lean-smt checkout.
#
# This script keeps the Java/JNI bridge sources in java-smt and injects the missing Lean
# integration overlay (`SmtJNI.lean`) into the upstream lean-smt checkout before building.
#
# Usage:
#   ./build/build-publish-solvers/build-leansmt-runtime-from-source.sh /absolute/path/to/lean-smt
#
# Result:
# - builds the upstream Lean-generated shared libraries (for example
#   .lake/build/lib/libsmt_SmtJNI.so) in the lean-smt checkout
# - builds build/libleansmt_jni.so in the lean-smt checkout
# - packages the runtime into java-smt/lib/native/x86_64-linux via package-leansmt-runtime.sh

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /absolute/path/to/lean-smt" >&2
  exit 1
fi

JAVA_SMT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
LEANSMT_DIR="$(cd "$1" && pwd)"
OVERLAY_DIR="$JAVA_SMT_DIR/build/build-publish-solvers/leansmt-overlay"
SOURCES_DIR="$JAVA_SMT_DIR/lib/native/source/libleansmt"

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

require_dir() {
  local path="$1"
  if [[ ! -d "$path" ]]; then
    echo "Missing required directory: $path" >&2
    exit 1
  fi
}

detect_java_home() {
  if [[ -n "${JAVA_HOME:-}" && -d "${JAVA_HOME}/include" ]]; then
    printf '%s\n' "$JAVA_HOME"
    return 0
  fi

  local javac_path
  javac_path="$(command -v javac || true)"
  if [[ -n "$javac_path" ]]; then
    javac_path="$(readlink -f "$javac_path")"
    printf '%s\n' "$(cd "$(dirname "$javac_path")/.." && pwd)"
    return 0
  fi

  echo "Could not determine JAVA_HOME" >&2
  exit 1
}

detect_lean_sysroot() {
  local sysroot
  sysroot="$(cd "$LEANSMT_DIR" && lake env lean --print-prefix)"
  if [[ -z "$sysroot" || ! -d "$sysroot" ]]; then
    echo "Could not determine Lean sysroot from lake env lean --print-prefix" >&2
    exit 1
  fi
  printf '%s\n' "$sysroot"
}

patch_lakefile() {
  local lakefile="$LEANSMT_DIR/lakefile.lean"
  if ! rg -q '^lean_lib SmtJNI\b' "$lakefile"; then
    cat >>"$lakefile" <<'EOF'

lean_lib SmtJNI where
  precompileModules := true
EOF
  fi
}

require_dir "$LEANSMT_DIR"
require_file "$LEANSMT_DIR/lakefile.lean"
require_file "$OVERLAY_DIR/SmtJNI.lean"
require_file "$SOURCES_DIR/leansmt_wrapper.c"
require_file "$SOURCES_DIR/leansmt_wrap.c"
require_file "$SOURCES_DIR/leansmt_wrapper.h"
require_cmd lake
require_cmd gcc
require_cmd patchelf
require_cmd rg
require_cmd readlink

JAVA_HOME_DETECTED="$(detect_java_home)"
LEAN_SYSROOT="$(detect_lean_sysroot)"
JAVA_INCLUDE_OS="linux"

cp -f "$OVERLAY_DIR/SmtJNI.lean" "$LEANSMT_DIR/SmtJNI.lean"
patch_lakefile

(
  cd "$LEANSMT_DIR"
  lake build SmtJNI:shared
)

require_file "$LEANSMT_DIR/.lake/build/lib/libsmt_SmtJNI.so"
require_file "$LEANSMT_DIR/.lake/build/lib/libsmt_Smt.so"
require_file "$LEANSMT_DIR/.lake/packages/auto/.lake/build/lib/libauto_Auto.so"
require_file "$LEANSMT_DIR/.lake/packages/Qq/.lake/build/lib/libQq_Qq.so"
require_file "$LEANSMT_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"
require_file "$LEAN_SYSROOT/lib/lean/libleanshared.so"

mkdir -p "$LEANSMT_DIR/build"

gcc -shared -fPIC \
  -I"$JAVA_HOME_DETECTED/include" \
  -I"$JAVA_HOME_DETECTED/include/$JAVA_INCLUDE_OS" \
  -I"$LEAN_SYSROOT/include" \
  -o "$LEANSMT_DIR/build/libleansmt_jni.so" \
  "$SOURCES_DIR/leansmt_wrapper.c" \
  "$SOURCES_DIR/leansmt_wrap.c" \
  -L"$LEANSMT_DIR/.lake/build/lib" \
  -L"$LEANSMT_DIR/.lake/packages/auto/.lake/build/lib" \
  -L"$LEANSMT_DIR/.lake/packages/Qq/.lake/build/lib" \
  -L"$LEANSMT_DIR/.lake/packages/cvc5/.lake/build/lib" \
  -L"$LEAN_SYSROOT/lib/lean" \
  -l:libsmt_SmtJNI.so -l:libsmt_Smt.so -l:libauto_Auto.so -l:libQq_Qq.so -l:libcvc5_cvc5.so -l:libleanshared.so \
  -Wl,-rpath,'$ORIGIN' \
  -Wl,-rpath,"$LEANSMT_DIR/.lake/build/lib" \
  -Wl,-rpath,"$LEANSMT_DIR/.lake/packages/auto/.lake/build/lib" \
  -Wl,-rpath,"$LEANSMT_DIR/.lake/packages/Qq/.lake/build/lib" \
  -Wl,-rpath,"$LEANSMT_DIR/.lake/packages/cvc5/.lake/build/lib" \
  -Wl,-rpath,"$LEAN_SYSROOT/lib/lean"

"$JAVA_SMT_DIR/build/build-publish-solvers/package-leansmt-runtime.sh" "$LEANSMT_DIR"

echo
echo "LeanSMT runtime rebuilt from source and packaged into java-smt."
echo "lean-smt checkout: $LEANSMT_DIR"
echo "Lean sysroot: $LEAN_SYSROOT"
echo "JAVA_HOME: $JAVA_HOME_DETECTED"
