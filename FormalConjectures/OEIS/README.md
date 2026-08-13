# OEIS Formalization Guidelines

This directory contains formalizations of conjectures and theorems associated with integer sequences from the [On-Line Encyclopedia of Integer Sequences (OEIS)](https://oeis.org/).

When contributing to or reviewing formalizations in this directory, please follow the specific conventions outlined below in addition to the general repository guidelines in [`AGENTS.md`](../../AGENTS.md).

## File Naming & Work-in-Progress (WIP) Status

- **Naming**: Files must be named after their OEIS number **without leading zeros** (e.g., `56777.lean`, `308734.lean`).

## Sequence and Auxiliary Definition Naming

Follow Mathlib's naming and capitalization conventions:
- **Primary Sequence**:
  - **Value sequences (`ℕ → ℕ`, `ℕ → ℚ`, etc.)**: Use lowercase `a` (`def a (n : ℕ) : ℕ := ...`). Secondary auxiliary sequences may be named `b`, `c`, etc.
  - **Predicate sequences (`ℕ → Prop`)**: Use capital `A` (`def A (n : ℕ) : Prop := ...`). Secondary auxiliary predicates may be named `B`, `C`, etc.
  - Do not name sequence functions after the OEIS number itself (e.g., do not use `A224515`).
- **Auxiliary Definitions**:
  - Functions returning non-`Prop` values must use `lowerCamelCase` (e.g., `catalanReciprocalSum`, `continuedFractionDenominator`, `kthPrimeFactor`, `reverseNat`, `middleColumnBit`).
  - Types, structures, and predicates returning `Prop` or `Type` must use `UpperCamelCase` (e.g., `IndexCond`, `IsCarmichaelNumber`, `IsAbsoluteEulerPseudoprime`).
- **Theorems and Lemmas**:
  - Must use `snake_case` (e.g., `a_ten_mul_add_two_eq`, `catalanReciprocalSum_fracPart_inj`, `tendsto_aReal_asymptotic`).

## Computability and `noncomputable`

- **Avoid unnecessary `noncomputable`**: Only mark definitions as `noncomputable` when strictly required by Lean's compiler (e.g., definitions depending on real numbers $\mathbb{R}$, `sInf` on unbounded subsets of $\mathbb{N}$, `PowerSeries.X`, `Nat.nth`, or classical choice/`Nat.find` over general undecidable propositions).
- **Prefer executable code**: If a sequence or helper is defined using computable operations—such as rational arithmetic ($\mathbb{Q}$), finite set operations (`Finset.sum`, `Finset.min'`), or structural/well-founded recursion on $\mathbb{N}$—it should be defined with `def` rather than `noncomputable def`.

## Classical Decidability & `open Classical`

- **Avoid top-level `open Classical`**: Do not use `open Classical` or `open scoped Classical` at the namespace or file level, as this triggers the `linter.style.openClassical` warning and causes build failures under `--wfail`.
- **Scoped Usage**:
  - For definitions that need classical decidability, use `open Classical in` scoped directly to that definition (placed before the docstring).
  - For proofs, use the `classical` tactic inside the proof body.
  - Alternatively, explicitly supply instances such as `have : Decidable ... := Classical.dec _` or `Classical.decPred _`.

## Namespaces

Every file must enclose all its declarations within a dedicated namespace matching `OeisA[Number]` (without leading zeros). This namespace should open immediately after the imports and module docstring, and close at the very end of the file.

```lean
namespace OeisA308734

-- definitions, helper lemmas, term theorems, and main conjecture

end OeisA308734
```

## Module Docstrings & References

Every file must include a descriptive module docstring (`/-! ... -/`) immediately following the imports.
- **Title**: By default, orient the title on the title/name of the OEIS entry, making it concise, descriptive, and properly LaTeX-formatted for any mathematical expressions (e.g., `# Reversible multiples $a(3^n) = 10^{3^{n-2}} - 1$ for powers of $3$` or `# Realization of primes $p \equiv \pm 1 \pmod{10}$ by continued fraction denominators`). Avoid generic placeholders like `# Conjectures associated with A123456`.
- **Content**: The module docstring should contain only a clear mathematical description of the sequence itself. It must **not** duplicate the docstrings of the conjecture(s), as a file may formalize multiple conjectures or variants. Do not include internal technical details or private helper implementations in the module introduction.
- **Math Formatting**: All mathematical symbols and expressions throughout docstrings must use LaTeX delimiters (`$ ... $` or `$$ ... $$`).
- **No Redundant Prefixes**: Do not include redundant prefixes like `A123456: ...` or `a: ...` in the docstrings of `def a` or helper functions.
- **References**: The module docstring must conclude with a standardized `*References:*` section containing a Markdown link to the official OEIS page, along with any other papers or articles necessary to formulate the problem.

```lean
/-!
# Number of representations of $n$ as $(2^a 3^b)^2 + (2^c 5^d)^2 + x^2 + y^2$

The number of representations of $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a, b, c, d, x, y$ are nonnegative integers.

*References:*
- [A308734](https://oeis.org/A308734)
- Z.-W. Sun, ["Refining Lagrange's four-square theorem"](https://doi.org/10.1016/j.jnt.2016.11.008), *J. Number Theory* **175** (2017), 167-190.
-/
```

## Main Theorem Docstrings

The main problem or conjecture (typically the last theorem in the file) must have a dedicated docstring (`/-- ... -/`).
- **Verbatim Citation**: The docstring must cite the conjecture from OEIS verbatim.
- **Proof Attribution**: For solved problems where a formal proof is referenced via `@[formal_proof ...]`, the bottom of the docstring should give attribution explaining where the proof comes from or what methods were used (whether AI-generated or human-authored). This can be a link or something like "solved by [name of AI system] prompted by [name of human]".

```lean
/--
Conjecture: Any integer $n > 1$ can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
where $a, b, c, d, x, y$ are nonnegative integers. - _Zhi-Wei Sun_, Jun 12 2018

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at ...]
theorem conjecture (n : ℕ) (hn : 1 < n) : A n := by
```

## Term Theorems (`category test`)

To ensure the formalized definition behaves correctly and matches the official OEIS sequence, every file **must include term theorems verifying the initial values of the sequence**.

- **Quantity**: Aim for around 5 test theorems, or more if all leading terms are zero (to ensure non-zero values are verified as well).
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
