#!/usr/bin/env bash
# Unfortunately `lake exe mk_all` doesn't preserve copyright comments
set -e

MODULE="FormalConjecturesForMathlib"
FILE="${MODULE}.lean"
TMP="${FILE}.tmp"

trap 'rm -f "$TMP"' EXIT

HEADER=$(sed -n -e '1,/-\//p' -e "1,/-\//! w $TMP" "$FILE")
mv "$TMP" "$FILE"

EXIT_CODE=0
lake exe mk_all --module --lib "$MODULE" || EXIT_CODE=$?

{ printf "%s\n" "$HEADER"; cat "$FILE"; } > "$TMP"
mv "$TMP" "$FILE"

exit "$EXIT_CODE"
