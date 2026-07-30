# Scripts

## Lean comment corpus

Generate the plain-text Lean comment corpus used with `codespell`:

```bash
python3 scripts/extract_documentation.py
codespell docs/lean_comments.txt
```

After correcting a spelling in the original Lean source, regenerate the corpus.
Use the following in CI or before committing to ensure the checked-in corpus is
current without modifying it:

```bash
python3 scripts/extract_documentation.py --check
```

Run the extractor tests with:

```bash
python3 -m unittest scripts.tests.test_extract_documentation
```
