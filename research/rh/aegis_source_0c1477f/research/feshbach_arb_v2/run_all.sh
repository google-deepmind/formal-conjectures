#!/usr/bin/env bash
# General-L Feshbach certificate.  Usage: ./run_all.sh L N NP c_target Xi0 slack_step m_cert mu [zero_cell=0.05]
# L = 1.2 certificate: ./run_all.sh 1.2 100 10000 2.0 450 1.0 1.98 5e-5
set -euo pipefail
L=$1; N=$2; NP=$3; CT=$4; XI0=$5; STEP=$6; M=$7; MU=$8; Z0=${9:-0.05}
cd "$(dirname "$0")"; OUT="L$L"; mkdir -p "$OUT"; cp *.py "$OUT"/; cd "$OUT"
python3 complement_lp.py "$L" "$CT" "$XI0" "$STEP" "$Z0"                       # complement_lp.json, sbar.json
python3 verify_krein_slack_arb.py complement_lp.json "$M" 3000 "$Z0" sbar.json > krein_slack.log
python3 complement_trace_arb.py "$L" "$N" sbar.json > trace.log            # trace_arb.json
python3 feshbach_blocks_arb.py "$L" "$N" "$NP" > blocks.log                # blocks_N${N}_NP${NP}.json
# exact decimal strictly below the certified lower bound (a ball-valued c_inf inflates the Cholesky radii)
CINF=$(python3 -c "import json, math; from flint import arb; t=json.load(open('trace_arb.json')); v=float((arb('$M')-arb(t['trPTP_upper'])).lower().mid()); print(f'{math.floor(v*1e11)/1e11 - 1e-11:.11f}')")
python3 schur_arb.py "blocks_N${N}_NP${NP}.json" "$CINF" "$MU" | tee schur.log
rm -f *.py; rm -rf __pycache__
