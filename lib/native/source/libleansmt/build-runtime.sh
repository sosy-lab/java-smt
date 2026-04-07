#!/usr/bin/env bash
set -euo pipefail

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

usage() {
  cat >&2 <<'EOF'
Usage: ./lib/native/source/libleansmt/build-runtime.sh /absolute/path/to/lean-smt

Build the pinned LeanSMT Linux x64 runtime in a throwaway worktree and stage it for JavaSMT.

The script:
- copies the upstream lean-smt checkout into build/lean-smt-work
- injects the JavaSMT Lean overlay without mutating the source checkout
- stages the runtime into build/leansmt-staging/x64
- refreshes the LeanSMT symlinks in lib/native/x86_64-linux

Set LEANSMT_SKIP_PIN_CHECK=1 only for local experiments with a non-pinned lean-smt commit.
EOF
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
LOCK_FILE="$SCRIPT_DIR/lean-smt.lock"
OVERLAY_FILE="$REPO_ROOT/build/build-publish-solvers/leansmt-overlay/SmtJNI.lean"
WORK_DIR="$REPO_ROOT/build/lean-smt-work"
STAGE_DIR="$REPO_ROOT/build/leansmt-staging/x64"
NATIVE_DIR="$REPO_ROOT/lib/native/x86_64-linux"
STAGE_LINK_PREFIX="../../../build/leansmt-staging/x64"

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

ensure_linux_x64() {
  local os arch
  os="$(uname -s)"
  arch="$(uname -m)"
  if [[ "$os" != "Linux" ]]; then
    echo "LeanSMT runtime build is supported only on Linux. Current OS: $os" >&2
    exit 1
  fi
  case "$arch" in
    x86_64|amd64) ;;
    *)
      echo "LeanSMT runtime build is supported only on Linux x64. Current arch: $arch" >&2
      exit 1
      ;;
  esac
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
  local checkout_dir="$1"
  local sysroot
  sysroot="$(cd "$checkout_dir" && lake env lean --print-prefix)"
  if [[ -z "$sysroot" || ! -d "$sysroot" ]]; then
    echo "Could not determine Lean sysroot from lake env lean --print-prefix" >&2
    exit 1
  fi
  printf '%s\n' "$sysroot"
}

patch_lakefile() {
  local lakefile="$1"
  if ! rg -q '^lean_lib SmtJNI\b' "$lakefile"; then
    cat >>"$lakefile" <<'EOF'

lean_lib SmtJNI where
  precompileModules := true
EOF
  fi
}

find_first_existing() {
  local candidate
  for candidate in "$@"; do
    if [[ -n "$candidate" && -f "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

find_first_executable() {
  local candidate
  for candidate in "$@"; do
    if [[ -n "$candidate" && -x "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

sync_worktree() {
  local source_dir="$1"
  if [[ "$source_dir" == "$WORK_DIR" ]]; then
    echo "Source checkout must not be inside $WORK_DIR" >&2
    exit 1
  fi

  rm -rf "$WORK_DIR"
  mkdir -p "$(dirname "$WORK_DIR")"
  cp -a "$source_dir" "$WORK_DIR"
}

stage_file() {
  local src="$1"
  local dest_name="${2:-$(basename "$src")}"
  cp -f "$src" "$STAGE_DIR/$dest_name"
}

remove_legacy_native_layout() {
  rm -f \
    "$NATIVE_DIR/libleansmt_jni.so" \
    "$NATIVE_DIR/libleansmt_jni.real.so" \
    "$NATIVE_DIR/libsmt_SmtJNI.so" \
    "$NATIVE_DIR/libsmt_Smt.so" \
    "$NATIVE_DIR/libauto_Auto.so" \
    "$NATIVE_DIR/libQq_Qq.so" \
    "$NATIVE_DIR/libcvc5_cvc5.so" \
    "$NATIVE_DIR/libleanshared.so" \
    "$NATIVE_DIR/cvc5" \
    "$NATIVE_DIR/libSmtJNI.so" \
    "$NATIVE_DIR/libSmt.so" \
    "$NATIVE_DIR/libAuto.so" \
    "$NATIVE_DIR/libQq.so" \
    "$NATIVE_DIR/libcvc5.so"
  rm -rf "$NATIVE_DIR/leansmt-runtime"
}

link_native_file() {
  local file_name="$1"
  ln -sfn "$STAGE_LINK_PREFIX/$file_name" "$NATIVE_DIR/$file_name"
}

if [[ $# -ne 1 ]]; then
  usage
  exit 1
fi

require_file "$LOCK_FILE"
require_file "$OVERLAY_FILE"
require_file "$SCRIPT_DIR/leansmt_wrapper.c"
require_file "$SCRIPT_DIR/leansmt_wrap.c"
require_file "$SCRIPT_DIR/leansmt_wrapper.h"
require_file "$SCRIPT_DIR/leansmt_extra_jni.c"

# shellcheck disable=SC1090
source "$LOCK_FILE"

SOURCE_DIR="$(cd "$1" && pwd)"
require_dir "$SOURCE_DIR"
require_file "$SOURCE_DIR/lakefile.lean"
require_file "$SOURCE_DIR/lean-toolchain"

ensure_linux_x64
require_cmd gcc
require_cmd git
require_cmd lake
require_cmd readlink
require_cmd rg
require_cmd javac

SOURCE_COMMIT=""
if git -C "$SOURCE_DIR" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  SOURCE_COMMIT="$(git -C "$SOURCE_DIR" rev-parse HEAD)"
  if [[ "${LEANSMT_SKIP_PIN_CHECK:-0}" != "1" && "$SOURCE_COMMIT" != "$LEANSMT_COMMIT" ]]; then
    cat >&2 <<EOF
LeanSMT checkout is at $SOURCE_COMMIT, but JavaSMT expects:
  $LEANSMT_COMMIT

Use the pinned checkout for reproducible builds:
  git -C "$SOURCE_DIR" fetch origin
  git -C "$SOURCE_DIR" checkout $LEANSMT_COMMIT

Set LEANSMT_SKIP_PIN_CHECK=1 only for local experiments.
EOF
    exit 1
  fi
fi

JAVA_HOME_DETECTED="$(detect_java_home)"

sync_worktree "$SOURCE_DIR"
cp -f "$OVERLAY_FILE" "$WORK_DIR/SmtJNI.lean"
patch_lakefile "$WORK_DIR/lakefile.lean"

(
  cd "$WORK_DIR"
  lake build SmtJNI:shared
)

LEAN_SYSROOT="$(detect_lean_sysroot "$WORK_DIR")"
SMT_JNI_SOURCE="$WORK_DIR/.lake/build/lib/libsmt_SmtJNI.so"
SMT_SOURCE="$WORK_DIR/.lake/build/lib/libsmt_Smt.so"
AUTO_SOURCE="$WORK_DIR/.lake/packages/auto/.lake/build/lib/libauto_Auto.so"
QQ_SOURCE="$WORK_DIR/.lake/packages/Qq/.lake/build/lib/libQq_Qq.so"
CVC5_LIB_SOURCE="$WORK_DIR/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"
LEAN_SHARED_SOURCE="$(find_first_existing \
  "$WORK_DIR/.lake/packages/lean4/build/lib/lean/libleanshared.so" \
  "$LEAN_SYSROOT/lib/lean/libleanshared.so")"
CVC5_BIN_SOURCE="$(find_first_executable \
  "$WORK_DIR/.lake/packages/cvc5/.lake/build/bin/cvc5" \
  "$WORK_DIR/.lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5" \
  "$(find "$WORK_DIR/.lake/packages/cvc5" -path '*/bin/cvc5' 2>/dev/null | head -n 1)")"

require_file "$SMT_JNI_SOURCE"
require_file "$SMT_SOURCE"
require_file "$AUTO_SOURCE"
require_file "$QQ_SOURCE"
require_file "$CVC5_LIB_SOURCE"
require_file "$LEAN_SHARED_SOURCE"
require_file "$CVC5_BIN_SOURCE"

rm -rf "$STAGE_DIR"
mkdir -p "$STAGE_DIR" "$NATIVE_DIR"

stage_file "$SMT_JNI_SOURCE"
stage_file "$SMT_SOURCE"
stage_file "$AUTO_SOURCE"
stage_file "$QQ_SOURCE"
stage_file "$CVC5_LIB_SOURCE"
stage_file "$LEAN_SHARED_SOURCE"
stage_file "$CVC5_BIN_SOURCE" "cvc5"
chmod +x "$STAGE_DIR/cvc5"

gcc -shared -fPIC -O2 \
  -I"$JAVA_HOME_DETECTED/include" \
  -I"$JAVA_HOME_DETECTED/include/linux" \
  -I"$LEAN_SYSROOT/include" \
  -o "$STAGE_DIR/libleansmt_jni.so" \
  "$SCRIPT_DIR/leansmt_wrapper.c" \
  "$SCRIPT_DIR/leansmt_extra_jni.c" \
  "$SCRIPT_DIR/leansmt_wrap.c" \
  -L"$STAGE_DIR" \
  -l:libsmt_SmtJNI.so \
  -l:libsmt_Smt.so \
  -l:libauto_Auto.so \
  -l:libQq_Qq.so \
  -l:libcvc5_cvc5.so \
  -l:libleanshared.so \
  -Wl,-rpath,'$ORIGIN'

remove_legacy_native_layout
link_native_file "libleansmt_jni.so"
link_native_file "libsmt_SmtJNI.so"
link_native_file "libsmt_Smt.so"
link_native_file "libauto_Auto.so"
link_native_file "libQq_Qq.so"
link_native_file "libcvc5_cvc5.so"
link_native_file "libleanshared.so"
link_native_file "cvc5"

echo "LeanSMT runtime staged in: $STAGE_DIR"
echo "LeanSMT symlinks refreshed in: $NATIVE_DIR"
echo "Lean sysroot: $LEAN_SYSROOT"
echo "JAVA_HOME: $JAVA_HOME_DETECTED"
if [[ -n "$SOURCE_COMMIT" ]]; then
  echo "lean-smt commit: $SOURCE_COMMIT"
fi
