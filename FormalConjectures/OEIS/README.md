# OEIS Formalization Guidelines

This directory contains formalizations of conjectures and theorems associated with integer sequences from the [On-Line Encyclopedia of Integer Sequences (OEIS)](https://oeis.org/).

When contributing to or reviewing formalizations in this directory, please follow the specific conventions outlined below in addition to the general repository guidelines in [`AGENTS.md`](../../AGENTS.md).

## File Naming & Work-in-Progress (WIP) Status

- **Naming**: Files must be named after their OEIS number **without leading zeros** (e.g., `56777.lean`, `308734.lean`).
- **WIP Files**: Newly added automated formalizations or unpolished problems should use the `.wip.lean` extension (e.g., `28859.wip.lean`). Once fully verified, degolfed, and audited, they can be renamed to `.lean`.

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

## Term Theorems (`category test`)

To ensure the formalized definition behaves correctly and matches the official OEIS sequence, every file **must include term theorems verifying the first few values of the sequence** (typically the first 5 values).

- **Official Alignment**: Verify the starting index ($n=0, 1, 2, \dots$) and exact initial values against the official OEIS `b-file` (`https://oeis.org/A[padded_number]/b[padded_number].txt`).
- **Attributes**: Every term theorem must be tagged with `@[category test, AMS 11]` (or another appropriate AMS subject).
- **Computable Definitions**: If the sequence definition is kernel-computable, prove the term theorems using `by rfl`, `by decide`, `by norm_num`, or by unfolding the definition.
- **Noncomputable Definitions**: For complex or `noncomputable` definitions where kernel evaluation is not possible:
  - Use appropriate helper lemmas to establish values rigorously (e.g., `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for `sInf`-based definitions, or `Int.floor_eq_iff` for real number bounds).
  - If the proof is still a work in progress in a `.wip.lean` file, `by sorry` is acceptable for the test lemmas until a full proof is constructed.

```lean
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by rfl
```

## Linter Control for Supporting Lemmas

Supporting definitions and helper lemmas should not be cluttered with `category` or `AMS` attributes. Instead, silence the style linters at the top of the namespace, and explicitly annotate only the term theorems (`category test`) and the main conjecture (`category research open` or `category research solved`).

```lean
namespace OeisA62567

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

-- [Supporting definitions and helper lemmas here...]

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by ...

@[category research solved, AMS 11]
theorem target_theorem_0 : ... := by ...

end OeisA62567
```

## Mathematical Faithfulness & Implementation Best Practices

- **Avoid Tautologies**: Ensure the main conjecture is not a trivial restatement of a recursive definition or a placeholder function. The formalization must be a faithful representation of the actual open or solved mathematical problem.
- **Rigorous Fuel**: When implementing bounded searches or trial division to keep functions kernel-computable, use mathematically rigorous fuel (e.g., bounding the search via Euclid's theorem or known mathematical limits) rather than arbitrary large constants like `100000`. This ensures both clean structural recursion and absolute mathematical correctness for proofs.
