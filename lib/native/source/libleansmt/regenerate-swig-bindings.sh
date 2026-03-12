#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
JAVA_OUT_DIR="$REPO_ROOT/src/org/sosy_lab/java_smt/solvers/leansmt"
INTERFACE_FILE="$SCRIPT_DIR/leansmt.i"
OUTPUT_C_FILE="$SCRIPT_DIR/leansmt_wrap.c"
JAVA_PACKAGE="org.sosy_lab.java_smt.solvers.leansmt"

if ! command -v swig >/dev/null 2>&1; then
  echo "Error: swig is not installed or not in PATH." >&2
  echo "Install on Debian/Ubuntu with: sudo apt-get install -y swig" >&2
  exit 1
fi

if [[ ! -f "$INTERFACE_FILE" ]]; then
  echo "Error: missing interface file: $INTERFACE_FILE" >&2
  exit 1
fi

if [[ ! -d "$JAVA_OUT_DIR" ]]; then
  echo "Error: missing Java output directory: $JAVA_OUT_DIR" >&2
  exit 1
fi

echo "Regenerating LeanSMT SWIG bindings..."
echo "  Interface: $INTERFACE_FILE"
echo "  C output : $OUTPUT_C_FILE"
echo "  Java out : $JAVA_OUT_DIR"

swig \
  -java \
  -package "$JAVA_PACKAGE" \
  -outdir "$JAVA_OUT_DIR" \
  -o "$OUTPUT_C_FILE" \
  "$INTERFACE_FILE"

echo "Done. Regenerated files:"
echo "  - $OUTPUT_C_FILE"
echo "  - $JAVA_OUT_DIR/LeanSMT.java"
echo "  - $JAVA_OUT_DIR/LeanSMTJNI.java"
echo "  - $JAVA_OUT_DIR/LeanSMTConstants.java"
echo
echo "Next step: review generated diffs before committing."

