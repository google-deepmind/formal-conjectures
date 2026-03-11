# Fix Review Issues

You are a PhD-level mathematician and Lean 4 expert. Your task is to fix all issues identified in a review for Erdős Problem **NUM**.

## Inputs

- **Review:** `ai-review/NUM.md`
- **Lean file:** `FormalConjectures/ErdosProblems/NUM.lean`
- **Library:** `FormalConjecturesForMathlib/` (shared definitions to reuse)
- **Website:** `https://www.erdosproblems.com/NUM` (authoritative source for citations and variants)

## Instructions

Read the review at `ai-review/NUM.md` in full. Then implement **all** fixes described below, working through each section in order. After completing all sections, run the verification checklist.

---

### Section 1: Code Reuse

If the review identifies local definitions that duplicate library code:

1. Find the library equivalent mentioned in the review (search `FormalConjecturesForMathlib/` and other problem files).
2. Read both the local definition and the library version. Confirm they are semantically equivalent or that the library version is strictly better.
3. Delete the local definition(s).
4. Add the necessary `import` statement(s) and `open` declarations.
5. Rewrite the theorem statement(s) to use the library definitions.
6. Ensure the file still compiles (`sorry` proofs are fine — the goal is correct *statements*, not proofs).

If the review says "No issues" or the section has no actionable recommendations, skip this section.

**Important constraints:**
- Only import definitions that already exist in the library or other problem files. Do **not** create new definitions in the library.
- Preserve the existing `ErdosNUM` namespace. Every problem file uses a `namespace ErdosNUM` / `end ErdosNUM` block — do not remove or rename it, even if the local definitions it originally scoped are deleted.

---

### Section 2: Citations

If the review identifies citation issues:

1. Fetch `https://www.erdosproblems.com/NUM` to get the authoritative reference list.
2. For each citation issue flagged in the review:
   - **Missing reference:** Add it to the module docstring in the standard format: `[TAG] Last, F., Last, F., _Title_. Journal **vol** (year), pages.`
   - **Incomplete reference:** Expand it with title, journal, volume, and page numbers. Use the website and cross-reference with other problem files for formatting examples.
   - **Tag mismatch:** Standardize the tag to match other files that cite the same paper. Search the codebase for the same author/year to find the canonical tag.
3. If the review mentions missing OEIS sequences or other cross-references from the website, add them to the docstring.

If the review says "No issues" or the section has no actionable recommendations, skip this section.

---

### Section 3: Variants

If the review identifies missing variants that should be formalized:

1. For each variant the review recommends adding:
   - Write a new theorem statement with an appropriate name (e.g., `erdos_NUM_upper`, `erdos_NUM_variant`).
   - Include a docstring explaining what the variant captures and its relationship to the main problem.
   - Use `sorry` for the proof.
   - Reuse existing definitions (library or local) — do not introduce new definitions unless necessary.
2. Only add variants that the review **explicitly recommends** formalizing. Do not invent new variants.

If the review says "No issues", the section has no actionable recommendations, or variants are described as "optional", skip this section.

---

### Section 4: Readability

If the review identifies readability improvements:

1. Apply each specific recommendation (e.g., renaming variables, using standard Lean/Mathlib idioms like `Odd k` instead of `k % 2 = 1`, replacing `p.1`/`p.2` with named projections).
2. Do **not** make readability changes that conflict with Section 1 fixes (e.g., don't improve a local definition that you already deleted and replaced with a library version).
3. Improve docstrings only if the review specifically requests it.

If the review says "No issues" or the section has no actionable recommendations, skip this section.

---

### Section 5: Formalizability

This section is informational. **No code changes needed** unless the review explicitly identifies an encoding issue that should be fixed (e.g., "the formalization encodes X but should encode Y"). In that case, fix the encoding in the theorem statement.

---

### Section 6: Correctness

If the review identifies correctness issues:

1. **This is the highest priority section.** Correctness fixes take precedence over all other changes.
2. For each issue flagged:
   - Read the review's explanation of why the current formalization is incorrect.
   - Identify the correct mathematical formulation (the review will typically describe it).
   - Rewrite the affected definition(s) and/or theorem statement(s).
   - If the fix involves switching to a library definition (overlapping with Section 1), ensure the library version is mathematically correct per the review's analysis.
3. If the review says "Correct and complete" or equivalent, no changes needed.

---

## Verification Checklist

After implementing all fixes, verify each item:

1. **Compiles:** Run `lake build FormalConjectures/ErdosProblems/NUM.lean` and confirm it compiles (with `sorry` proofs — warnings are OK, errors are not).
2. **Code reuse:** Grep the file for any local definitions the review said to remove. Confirm they are gone.
3. **Citations:** Re-read the module docstring. Confirm all references from the website are present with full bibliographic details.
4. **Variants:** If variants were added, confirm each has a docstring and compiles.
5. **Correctness:** If correctness issues were flagged, re-read the rewritten theorem statement and confirm it matches the review's recommended fix.
6. **No regressions:** Ensure no other files that import this one are broken. Search for `import FormalConjectures.ErdosProblems.NUM` across the codebase.

If compilation fails, diagnose and fix the error. Common issues:
- Missing imports (add `import` statements)
- Missing `open` declarations (add `open` for namespaces used)
- Type mismatches from switching definitions (adjust the theorem statement to match library types)
- Name clashes (use fully qualified names or adjust `open`/`namespace`)

## Output

When done, report a summary of changes made per section (1-6) and the result of each verification checklist item.
