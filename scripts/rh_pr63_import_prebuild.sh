#!/usr/bin/env bash
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
# Build the official RH target's imported V13 module without claiming RH.
set -euo pipefail
: "${AEGIS_BASE_SHA:?}"
: "${LI_PROVIDER_SHA:?}"
: "${MATHLIB_SHA:?}"
: "${LI_PROVIDER_ORIGINAL_MATHLIB_SHA:?}"
: "${LI_FACTORIZATION_BLOB:?}"
: "${LEAN_TOOLCHAIN:?}"

ROOT="$(pwd)"
BASE="$ROOT/.aegis-base/sovereign-omega-v2/formal/bridges/lean"
SRC="$ROOT/AegisRH/PR606/Source"
COMPAT="$ROOT/AegisRH/PR606/Compat"
LOCAL="$ROOT/AegisRH/PR606"
OUT="$ROOT/.lake/build/lib/lean"
ORDER="$RUNNER_TEMP/rh-pr63-imports.order"
AUDIT="$RUNNER_TEMP/RHPR63ImportAudit.lean"
AUDIT_LOG="$RUNNER_TEMP/rh-pr63-import-audit.log"

[[ "$(git -C .aegis-base rev-parse HEAD)" == "$AEGIS_BASE_SHA" ]]
[[ "$(git -C .li rev-parse HEAD)" == "$LI_PROVIDER_SHA" ]]
[[ "$(git -C .li hash-object Hadamard/General/Factorization.lean)" == "$LI_FACTORIZATION_BLOB" ]]
[[ "$(cat lean-toolchain)" == "$LEAN_TOOLCHAIN" ]]
grep -Fq "$MATHLIB_SHA" lake-manifest.json
[[ -f "$LOCAL/RHRestrictedWeilCriterionV13.lean" ]]
[[ -f "$SRC/RHMillenniumGateV10.lean" ]]
[[ -f "$COMPAT/RHZeroKernelLaplaceV12.lean" ]]

# Use PR63's own Source/Compat, never an older proof snapshot.
# A pinned provider cache can be reused; on a miss rebuild it with the
# exact same Mathlib/Lean compatibility substitutions as the direct replay.
if [[ ! -f .li/.lake/build/lib/lean/Lc/LiCriterion/HadamardBridge.olean ]]; then
  (
    cd .li
    printf '%s\n' "$LEAN_TOOLCHAIN" > lean-toolchain
    python3 - <<'PY'
import os
from pathlib import Path
p=Path('lakefile.lean')
s=p.read_text(encoding='utf-8')
old=os.environ['LI_PROVIDER_ORIGINAL_MATHLIB_SHA']
new=os.environ['MATHLIB_SHA']
assert s.count(old)==1
p.write_text(s.replace(old,new,1), encoding='utf-8')
q=Path('Hadamard/General/Factorization.lean')
s=q.read_text(encoding='utf-8')
for old,new in [
  ('eventually_nhdsWithin_of_forall fun w hw => ite_eq_right hw',
   'eventually_nhdsWithin_of_forall fun w hw => if_neg hw'),
  ('have hgz : g z = Q z := ite_eq_left rfl',
   'have hgz : g z = Q z := by simp [g]'),
  ('rw [ite_eq_right heq, hQ_eq_div z (hz heq)]',
   'rw [if_neg heq, hQ_eq_div z (hz heq)]'),
]:
    if old in s: s=s.replace(old,new,1)
q.write_text(s, encoding='utf-8')
PY
    rm -f lake-manifest.json
    lake update mathlib
    lake exe cache get
    lake build Hadamard.OrderOne.LogDerivMultiplicity \
      Lc.LiCriterion.XiGrowth \
      Lc.LiCriterion.HadamardSummabilityBridge \
      Lc.LiCriterion.HadamardBridge
  )
fi
[[ -f .li/.lake/build/lib/lean/Lc/LiCriterion/HadamardBridge.olean ]]
mkdir -p "$OUT"
cp -a .li/.lake/build/lib/lean/. "$OUT/"

# Match PR606's existing BASE < Source < Compat < local import precedence.
# Fail on missing files and cycles; do not alter proof statements.
python3 - "$BASE" "$SRC" "$COMPAT" "$LOCAL" "$ORDER" <<'PY'
from pathlib import Path
import sys
base, src, compat, local, out=map(Path, sys.argv[1:])
groups=[{p.stem:p for p in root.glob('*.lean')}
        for root in (base,src,compat,local)]
mods=set().union(*(set(g) for g in groups))
def chosen(name):
    for group in reversed(groups):
        if name in group: return group[name]
    raise SystemExit(f'RH_IMPORT_MISSING:{name}')
order=[]
visited=set()
active=set()
def visit(name):
    if name in visited: return
    if name in active: raise SystemExit(f'RH_IMPORT_CYCLE:{name}')
    active.add(name)
    for line in chosen(name).read_text(encoding='utf-8').splitlines():
        s=line.split('--',1)[0].strip()
        if not s.startswith('import '): continue
        for imported in s[7:].split():
            root=imported.split('.')[0]
            if root in mods: visit(root)
    active.remove(name)
    visited.add(name)
    order.append(name)
visit('RHRestrictedWeilCriterionV13')
out.write_text('\n'.join(order)+'\n', encoding='utf-8')
print('RH_PR63_IMPORT_CLOSURE_COUNT',len(order))
PY

ROOT_LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$OUT:$LOCAL:$COMPAT:$SRC:$BASE:$ROOT/.li/.lake/build/lib/lean:$ROOT_LEAN_PATH"
while IFS= read -r mod; do
  [[ -n "$mod" ]] || continue
  file="$BASE/$mod.lean"
  [[ -f "$SRC/$mod.lean" ]] && file="$SRC/$mod.lean"
  [[ -f "$COMPAT/$mod.lean" ]] && file="$COMPAT/$mod.lean"
  [[ -f "$LOCAL/$mod.lean" ]] && file="$LOCAL/$mod.lean"
  echo "RH_IMPORT_BUILD $mod $file"
  lean -o "$OUT/$mod.olean" "$file"
done < "$ORDER"

cat > "$AUDIT" <<'LEAN'
import RHRestrictedWeilCriterionV13
#print axioms AEGIS.RHRestrictedWeilCriterionV13.restricted_weil_criterion_v13
#print axioms AEGIS.RHRestrictedWeilCriterionV13.universal_zero_quadratic_implies_mathlib_rh_v13
#print axioms AEGIS.RHRestrictedWeilCriterionV13.certificate_of_universal_zero_quadratic_v13
LEAN
lean "$AUDIT" > "$AUDIT_LOG" 2>&1
python3 scripts/verify_rh_overlay_axioms.py "$AUDIT" "$AUDIT_LOG"

# Canary: native Lake must find all imported .olean files without custom paths.
unset LEAN_PATH
lake env lean "$AUDIT" > "$AUDIT_LOG" 2>&1
python3 scripts/verify_rh_overlay_axioms.py "$AUDIT" "$AUDIT_LOG"
echo 'RH_PR63_STANDARD_LAKE_IMPORT=PASS; OFFICIAL_UNIVERSAL_GOAL=OPEN'
