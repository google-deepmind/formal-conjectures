#!/usr/bin/env bash
# Convert all lean-eval problem files into FormalConjectures/LeanEval/
# and then run lake build to check compilation.
#
# Usage: bash scripts/convert_all_lean_eval.sh

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_EVAL_ROOT="${REPO_ROOT}/../lean-eval"
DEST_DIR="${REPO_ROOT}/FormalConjectures/LeanEval"
CONVERTER="${REPO_ROOT}/scripts/convert_lean_eval.py"

if [ ! -d "${LEAN_EVAL_ROOT}" ]; then
  echo "Error: lean-eval repo not found at ${LEAN_EVAL_ROOT}" >&2
  exit 1
fi

echo "=== Converting lean-eval problems ==="
echo "Source: ${LEAN_EVAL_ROOT}/LeanEval"
echo "Dest:   ${DEST_DIR}"
echo

# Find all .lean files in LeanEval/
total=0
converted=0

while IFS= read -r src_file; do
  # Get relative path from LeanEval/ root
  rel_path="${src_file#${LEAN_EVAL_ROOT}/LeanEval/}"
  dest_file="${DEST_DIR}/${rel_path}"

  total=$((total + 1))
  python3 "${CONVERTER}" "${src_file}" "${dest_file}"
  converted=$((converted + 1))
done < <(find "${LEAN_EVAL_ROOT}/LeanEval" -name '*.lean' -type f | sort)

echo
echo "=== Conversion complete: ${converted}/${total} files ==="
echo

# Now generate the import file for the LeanEval module
IMPORT_FILE="${REPO_ROOT}/FormalConjectures/LeanEval.lean"
echo "Generating import file: ${IMPORT_FILE}"
{
  echo "-- Auto-generated import file for LeanEval problems"
  find "${DEST_DIR}" -name '*.lean' -type f | sort | while IFS= read -r f; do
    rel="${f#${REPO_ROOT}/}"
    # Convert path to module name: FormalConjectures/LeanEval/Foo/Bar.lean -> FormalConjectures.LeanEval.Foo.Bar
    mod=$(echo "${rel}" | sed 's|/|.|g' | sed 's|\.lean$||')
    echo "import ${mod}"
  done
} > "${IMPORT_FILE}"

echo "Generated $(wc -l < "${IMPORT_FILE}") import lines"
echo
echo "=== Now building with lake ==="
