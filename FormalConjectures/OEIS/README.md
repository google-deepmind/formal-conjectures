# OEIS Formalization Guidelines

This directory contains formalizations of conjectures and theorems associated with integer sequences from the [On-Line Encyclopedia of Integer Sequences (OEIS)](https://oeis.org/).

When contributing to or reviewing formalizations in this directory, please follow the specific conventions outlined below in addition to the general repository guidelines in [`AGENTS.md`](../../AGENTS.md).

## File Naming & Work-in-Progress (WIP) Status

- **Naming**: Files must be named after their OEIS number **without leading zeros** (e.g., `56777.lean`, `308734.lean`).

## Sequence Definition Naming

The primary sequence in each OEIS file must follow exact Mathlib capitalization conventions based on its return type:
- **Value sequences (`ℕ → ℕ`, etc.)**: Use lowercase `a` (`def a (n : ℕ) : ℕ := ...`). Secondary auxiliary sequences may be named `b`, `c`, etc.
- **Predicate sequences (`ℕ → Prop`)**: Definitions returning `Prop` define properties/propositions and must use capital `A` (`def A (n : ℕ) : Prop := ...`). Secondary auxiliary predicates may be named `B`, `C`, etc.
Do not name the sequence function after the OEIS number itself (e.g. do not use `A224515`).

## Namespaces

Every file must enclose all its declarations within a dedicated namespace matching `OeisA[Number]` (without leading zeros). This namespace should open immediately after the imports and module docstring, and close at the very end of the file.

```lean
namespace OeisA308734

-- definitions, helper lemmas, term theorems, and main conjecture

end OeisA308734
```

## Module Docstrings & References

Every file must include a descriptive module docstring (`/-! ... -/`) immediately following the imports.
- **Content**: The docstring should clearly explain the sequence definition and the statement of the conjecture or theorem being formalized.
- **References**: It must conclude with a standardized `*References:*` (or `*Reference:*` for a single item) section containing a Markdown link to the official OEIS page, along with any other papers or articles necessary to formulate the problem.

```lean
/-!
# Four-square conjecture with powers of 2, 3, and 5

Any integer $n > 1$ can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
where $a, b, c, d, x, y$ are nonnegative integers.

*References:*
- [A308734](https://oeis.org/A308734)
- Z.-W. Sun, "Refining Lagrange's four-square theorem," *J. Number Theory* **175** (2017), 167-190.
-/
```

## Main Theorem Docstrings

The main problem or conjecture (typically the last theorem in the file) must have a dedicated docstring (`/-- ... -/`).
- **Verbatim Citation**: The docstring must cite the conjecture from OEIS verbatim.
- **Proof Attribution**: For solved problems where a formal proof is referenced via `@[formal_proof ...]`, the bottom of the docstring should give attribution explaining where the proof comes from or what methods were used (whether AI-generated or human-authored). This can be a link or something like "solved by [name of AI system] prompted by [name of human].

```lean
/--
Any integer $n > 1$ can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
where $a, b, c, d, x, y$ are nonnegative integers.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at ...]
theorem conjecture (n : ℕ) (hn : 1 < n) : A n := by
```

## Term Theorems (`category test`)

To ensure the formalized definition behaves correctly and matches the official OEIS sequence, every file **must include term theorems verifying the first few values of the sequence** (typically the first 5 values).

- **Naming**: Every term verification theorem for sequence `a` (or predicate `A`) must be named strictly `a_0`, `a_1`, `a_2`, etc., according to the index (`a_[n]`). Note that even when testing an `UpperCamelCase` property definition like `A`, Mathlib naming rules mandate lowercasing it right inside `snake_case` theorem names (`a_0 : A 0`, `a_1 : A 1`).
- **Official Alignment**: Verify the starting index ($n=0, 1, 2, \dots$) and exact initial values against the official OEIS `b-file` (`https://oeis.org/A[padded_number]/b[padded_number].txt`).
- **Attributes**: Every term theorem must be tagged with `@[category test, AMS 11]` (or another appropriate AMS subject).
- **Computable Definitions**: If the sequence definition is kernel-computable, prove the term theorems using `by rfl`, `by decide`, `by norm_num`, or by unfolding the definition.
- **Noncomputable Definitions**: For complex or `noncomputable` definitions where kernel evaluation is not possible:
  - Use appropriate helper lemmas to establish values rigorously (e.g., `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for `sInf`-based definitions, or `Int.floor_eq_iff` for real number bounds).

```lean
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl
```
