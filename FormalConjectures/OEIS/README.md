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
- **Title**: By default, orient the title on the title/name of the OEIS entry, making it concise, descriptive, and properly LaTeX-formatted for any mathematical expressions (e.g., `# Euclid-Mullin sequence` or `# Realization of primes $p \equiv \pm 1 \pmod{10}$ by continued fraction denominators`). Avoid generic placeholders like `# Conjectures associated with A123456`.
- **Content**: The module docstring should contain only a clear mathematical description of the sequence itself. It must **not** duplicate the docstrings of the conjecture(s), as a file may formalize multiple conjectures or variants. Do not include internal technical details or private helper implementations in the module introduction.
- **Math Formatting**: All mathematical symbols and expressions throughout docstrings must use LaTeX delimiters (`$ ... $` or `$$ ... $$`).
- **No Redundant Prefixes**: Do not include redundant prefixes like `A123456: ...` or `a: ...` in the docstrings of `def a` or helper functions.
- **References**: The module docstring must conclude with a standardized `*References:*` section containing a Markdown link to the official OEIS page, along with any other papers or articles necessary to formulate the problem.
```lean
/-!
# Euclid-Mullin sequence

The Euclid-Mullin sequence starts with $a(1) = 2$. Each subsequent term is the smallest prime
factor of one plus the product of all preceding terms. We extend the sequence by $a(0) = 1$ and
write $b(n)$ for the product of the first $n$ official terms.

*References:*
- [A000945](https://oeis.org/A000945)
- [Mullin63] A. A. Mullin,
  ["Research Problem 8 (ii)"](https://doi.org/10.1090/S0002-9904-1963-11017-4),
  *Bull. Amer. Math. Soc.* **69** (1963), p. 737.
- A. R. Booker, "A variant of the Euclid-Mullin sequence containing every prime,"
  [arXiv:1605.08929](https://arxiv.org/abs/1605.08929), *Journal of Integer Sequences* **19**
  (2016), Article 16.6.4.
-/
```

## Main Theorem Docstrings

The main problem or conjecture (typically the last theorem in the file) must have a dedicated
docstring (`/-- ... -/`).
- **Verbatim Citation**: The docstring must cite the conjecture from OEIS verbatim.
- **Proof Attribution**: For solved problems where a formal proof is referenced via
  `@[formal_proof ...]`, the bottom of the docstring should give attribution explaining where
  the proof comes from or what methods were used (whether AI-generated or human-authored). This can
  be a link or something like "solved by [name of AI system] prompted by [name of human]".

```lean
/--
"Does the sequence ... contain every prime? ... [It] was considered by Guy and Nowakowski
and later by Shanks, [Wagstaff93] computed the sequence through the 43rd term. The
computational problem inherent in continuing the sequence further is the enormous size of the
numbers that must be factored. Already the number $a(1) \cdots a(43) + 1$ has 180 digits."
- [CrandallPomerance01]

See also [Mullin63].
-/
@[category research open, AMS 11]
theorem every_prime_occurs :
    answer(sorry) ↔ ∀ p, p.Prime → ∃ n ≥ 1, a n = p := by
  sorry
```

## Multiple Conjectures in a Single Sequence

When an OEIS entry documents multiple distinct conjectures (e.g., Conjecture 1, Conjecture 2,
or general product/modulus variants):
- **Naming**: Disambiguate them using indexed names like `conjecture_1`, `conjecture_2`,
  `conjecture_3a`, etc., or descriptive identifiers (e.g., `conjecture_integrality`,
  `conjecture_supercongruence`).
- **Docstring Disambiguation**: Each theorem's docstring must explicitly identify which OEIS
  conjecture it matches and quote it verbatim.

## Term Theorems (`category test`)

To ensure the formalized definition behaves correctly and matches the official OEIS sequence,
every file **must include term theorems verifying the initial values of the sequence**.

- **Placement**: Term theorems must be placed **immediately following the definition of `a`**
  (or its immediate reduction/helper lemmas), preceding the main benchmark conjectures.
- **Quantity**: Aim for around 5 test theorems, or more if all leading terms are trivial (to ensure
  non-zero/non-one values are verified as well).
- **Naming**: Every term verification theorem for sequence `a` (or predicate `A`) must be named
  strictly `a_0`, `a_1`, `a_2`, etc., according to the index (`a_[n]`). Note that even when
  testing an `UpperCamelCase` property definition like `A`, Mathlib naming rules mandate
  lowercasing it right inside `snake_case` theorem names (`a_0 : A 0`, `a_1 : A 1`).
- **Official Alignment**: Verify the starting index ($n=0, 1, 2, \dots$) and exact initial values against the official OEIS `b-file` (`https://oeis.org/A[padded_number]/b[padded_number].txt`).
- **Attributes**: Every term theorem must be tagged with `@[category test, AMS 11]` (or another appropriate AMS subject).
- **Computable Definitions**: If the sequence definition is kernel-computable, prove the term theorems using `by rfl`, `by decide`, `by norm_num`, or by unfolding the definition.
- **Noncomputable Definitions**: For complex or `noncomputable` definitions where kernel evaluation is not possible:
  - Use appropriate helper lemmas to establish values rigorously (e.g., `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for `sInf`-based definitions, or `Int.floor_eq_iff` for real number bounds).

```lean
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by norm_num [a, b]

@[category test, AMS 11]
theorem a_4 : a 4 = 43 := by norm_num [a, b]
```
