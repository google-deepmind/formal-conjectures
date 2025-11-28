# Erdos updates helper

This directory holds the small tooling used by the repository to detect
updates on the Erdős problems website and open issues when problem pages
change.

Files
- `erdos_dates.json` — persisted map of `{ problem_id: last_seen_date }`.
- `README.md` — this file.
- `check_erdos_updates.py` — script that scans `*.lean` files under
  `FormalConjectures/ErdosProblems`, fetches the corresponding web page and
  extracts a last-updated date. The script is run by the GitHub Actions
  workflow `.github/workflows/erdos-watcher.yml`.

Running locally (recommended before enabling the workflow)

1. Install dependencies (use a virtualenv):

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install requests beautifulsoup4 python-dateutil
```

2. Dry-run against the repository (will not write files):

```powershell
# using the convenience script (recommended)
.\scripts\run_erdos_check.ps1

# or directly (dry-run)
python .github\scripts\check_erdos_updates.py \
  --problems-dir FormalConjectures/ErdosProblems \
  --dates-file .github/erdos-updates/erdos_dates.json \
  --out .github/erdos-updates/updates.json \
  --dry-run
```

3. Test parsing a single local HTML file (useful for tuning the parser):

```powershell
python .github\scripts\check_erdos_updates.py --sample-html .github/erdos-updates/examples/erdos_1.html --id 1 --lean-path FormalConjectures/ErdosProblems/1.lean
```

4. Install dependencies using the supplied `requirements.txt`:

```powershell
python -m venv .venv_erdos
.\.venv_erdos\Scripts\Activate.ps1
pip install -r .github/erdos-updates/requirements.txt
```

5. Use the VS Code tasks (if you use VS Code): open the Command Palette → `Tasks: Run Task` and choose `Erdos: Dry-run checker` or `Erdos: Full checker`.

Notes
- On the first run the script initializes `erdos_dates.json` and emits no
  update issues. This avoids creating issues for the whole existing dataset.
- If you improve the HTML date extraction logic, please update
  `.github/scripts/check_erdos_updates.py` and test locally using the
  `--sample-html` mode.

If you'd like, I can further refine the extraction logic to target the
exact HTML element used by the Erdős problems site — paste a sample HTML
snippet and I'll update the script accordingly.
