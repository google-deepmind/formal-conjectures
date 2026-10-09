#!/usr/bin/env bash
# Full reproduction of the L = 1.05 Feshbach certificate (python-flint 0.8, scipy/HiGHS for the LP).
set -euo pipefail
cd "$(dirname "$0")"
python3 complement_lp.py                                                  # complement_lp.json, sbar.json
python3 verify_krein_slack_arb.py complement_lp.json 0.99 3000 0.05 sbar.json | tee krein_slack.log
python3 complement_trace_arb.py 1.05 16 sbar.json | tee trace.log          # trace_arb.json
python3 feshbach_blocks_arb.py 1.05 16 10000 | tee blocks.log              # blocks_N16_NP10000.json
CINF=$(python3 -c "import json; from flint import arb; t=json.load(open('trace_arb.json')); print((arb('0.99')-arb(t['trPTP_upper'])).lower())")
python3 schur_arb.py blocks_N16_NP10000.json "$CINF" 0.0025 | tee schur.log
