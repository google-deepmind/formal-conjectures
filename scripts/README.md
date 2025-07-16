# Codex helper

The `run_single_file.py` script runs Codex inside Docker on a single file from this repository. It builds both `private_mathlib4` and `formal_conjectures` before invoking Codex.

Example:

```bash
GEMINI_API_KEY="" ./scripts/run_single_file.py \
  --prep FormalConjectures/Paper/CasasAlvero.lean \
  --export FormalConjectures/Paper/CasasAlvero.lean \
  run --auto-continuous --auto-continuous-first-doc \
  "lake build FormalConjectures/Paper/CasasAlvero.lean"
```

