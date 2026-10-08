#!/usr/bin/env bash
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
# Reuse PR606 exact import closure; compile the already-proved 693/2000 window
# into the same module search path without weakening the official RH target.
set -euo pipefail
ROOT="$(pwd)"
OUT="$1"
WINDOW_SHA="2c3d041b633147ec97c7ef753aa9d157a47bb9f5"
WBASE="$ROOT/.aegis-window/sovereign-omega-v2/formal/bridges/lean"
BASE="$ROOT/.aegis-base/sovereign-omega-v2/formal/bridges/lean"
SRC="$ROOT/AegisRH/PR606/Source"
COMPAT="$ROOT/AegisRH/PR606/Compat"
LOCAL="$ROOT/AegisRH/PR606"
if [[ -v RH_WINDOW_SRC_OVERRIDE ]]; then SRC="$RH_WINDOW_SRC_OVERRIDE"; fi
if [[ -v RH_WINDOW_COMPAT_OVERRIDE ]]; then COMPAT="$RH_WINDOW_COMPAT_OVERRIDE"; fi
OVERLAY="$ROOT/AEGISOverlay"
WIN="$ROOT/AegisRH/SmallWindow"
WORKTMP="/tmp"
if [[ -n "$RUNNER_TEMP" ]]; then WORKTMP="$RUNNER_TEMP"; fi
ORDER="$WORKTMP/rh-pr63-proved-window-closure.order"
AUDIT="$WORKTMP/rh-pr63-proved-window-axioms.lean"
LOG="$WORKTMP/rh-pr63-proved-window-axioms.log"
test "$(git -C "$ROOT/.aegis-window" rev-parse HEAD)" = "$WINDOW_SHA"
test -f "$OUT/RHRestrictedWeilCriterionV13.olean"
test -f "$WIN/RHSmallWindowCanonicalJoinV1.lean"
test -f "$OVERLAY/RHWindow693Over2000V1.lean"
mkdir -p "$OUT"

python3 - "$BASE" "$WBASE" "$SRC" "$COMPAT" "$LOCAL" "$OVERLAY" "$WIN" "$ORDER" "$OUT" <<'PY'
from pathlib import Path
import sys
base, wbase, src, compat, local, overlay, win, orderpath, out = map(Path, sys.argv[1:])
roots=(base, wbase, src, compat, local, overlay, win)
groups=[{p.stem:p for p in r.glob("*.lean")} for r in roots]
allmods=set().union(*(set(g) for g in groups))
def chosen(n):
    for group in reversed(groups):
        if n in group: return group[n]
    raise SystemExit(f"RH_WINDOW_SOURCE_MISSING:{n}")
done=set()
active=set()
order=[]
def visit(n):
    if n in done: return
    if n in active: raise SystemExit(f"RH_WINDOW_IMPORT_CYCLE:{n}")
    active.add(n)
    for ln in chosen(n).read_text(encoding="utf-8").splitlines():
        ln=ln.split("--",1)[0].strip()
        if not ln.startswith("import "): continue
        for dep in ln[7:].split():
            if dep in allmods:
                visit(dep)
            elif dep.startswith("AEGISOverlay.") and dep.split(".",1)[1] in allmods:
                visit(dep.split(".",1)[1])
            elif dep.startswith(("Mathlib.","FormalConjectures.","Lc.","Hadamard.")):
                continue
            elif dep.split(".")[0] in allmods:
                visit(dep.split(".")[0])
            else:
                raise SystemExit(f"RH_WINDOW_IMPORT_UNRESOLVED:{n}:{dep}")
    active.remove(n)
    done.add(n)
    order.append(n)
visit("RHSmallWindowCanonicalJoinV1")
order=[n for n in order if not (out / (n+".olean")).exists()]
orderpath.write_text("\n".join(f"{n}\t{chosen(n)}" for n in order)+"\n",encoding="utf-8")
print(f"RH_PROVED_WINDOW_BUILD_COUNT={len(order)}")
for n in order: print("RH_PROVED_WINDOW_SOURCE",n,str(chosen(n)))
PY
BASE_LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$OUT:$WIN:$OVERLAY:$LOCAL:$COMPAT:$SRC:$WBASE:$BASE:$ROOT/.li/.lake/build/lib/lean:$BASE_LEAN_PATH"
while IFS="$(printf '\t')" read -r name file; do
    test -n "$name" || continue
    echo "RH_PROVED_WINDOW_COMPILE $name $file"
    lean -o "$OUT/$name.olean" "$file"
done < "$ORDER"

cat > "$AUDIT" <<'LEAN'
import RHSmallWindowCanonicalJoinV1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.window_one_over_64_of_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.universal_zero_quadratic_of_above_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.riemannHypothesis_of_above_693_over_2000_v1
LEAN
lean "$AUDIT" > "$LOG" 2>&1
python3 "$ROOT/scripts/verify_rh_overlay_axioms.py" "$AUDIT" "$LOG"
echo 'RH_PROVED_WINDOW_IMPORT=PASS; LARGE_WINDOW_PREMISE=NOT_ASSUMED'
