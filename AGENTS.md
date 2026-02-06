# Agent Guidelines for Formal Conjectures

This document provides guidelines for AI agents working on the Formal Conjectures repository.

## Repository Structure

### Main Directories

- **`FormalConjectures/`**: Contains formalisations of conjectures, organized by source:
  - `ErdosProblems/` - Problems from [erdosproblems.com](https://www.erdosproblems.com/)
  - `Paper/` - Problems from research papers
  - `Arxiv/` - Problems from arXiv papers (organized by arXiv ID)
  - `Books/` - Problems from mathematics books
  - `Wikipedia/` - Problems from Wikipedia
  - Other sources as appropriate

- **`FormalConjectures/Util/`**: Repository infrastructure and utilities:
  - `Attributes/` - Defines the `category` and `AMS` attributes
  - `Answer.lean` - Implements the `answer()` elaborator for problems requiring answers
  - `Linters/` - Custom linters for the repository
  - `ProblemImports.lean` - Standard imports for problem files

- **`FormalConjecturesForMathlib/`**: Definitions, lemmas, and basic API suitable for upstreaming to Mathlib:
  - **IMPORTANT**: No `sorry` is allowed in this directory
  - Follows Mathlib's directory structure (e.g., `Topology/`, `Algebra/`, `NumberTheory/`)
  - Contains supporting definitions and lemmas needed for problem statements
  - Code here should be of Mathlib quality and eventually PR-able to Mathlib

## Formalisation Conventions

### Namespaces

Each problem file should define its content in a dedicated namespace:

```lean
namespace Erdos10

-- definitions, theorems, variants here

end Erdos10
```

For variants of a problem, use dotted notation within the same namespace:
```lean
theorem main_conjecture : ... := by sorry

theorem main_conjecture.variants.special_case : ... := by sorry
```

### The `category` Attribute

Every theorem/lemma should have exactly one `category` attribute indicating its type:

**Values:**
- `@[category high_school]` - High school level math problem
- `@[category undergraduate]` - Undergraduate level math problem
- `@[category graduate]` - Graduate level math problem
- `@[category research open]` - Open research problem (no accepted solution exists)
- `@[category research solved]` - Solved research problem (informal proof widely accepted)
- `@[category research formally solved using <kind> at "link"]` - Formally solved problem
  - `<kind>` must be one of: `formal_conjectures`, `lean4`, or `other_system`
- `@[category test]` - Sanity check or unit test for definitions
- `@[category API]` - Basic theory around a new definition

**Examples:**
```lean
@[category research open, AMS 11]
theorem riemann_hypothesis : ... := by sorry

@[category test, AMS 11]
theorem sanity_check : ¬ SomeBadProperty := by sorry

@[category API]
lemma basic_property_of_new_definition : ... := by exact ...
```

### The `AMS` Attribute

Every problem should have at least one AMS subject classification number from the [AMS MSC2020](https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf).

**Common subjects:**
- `3` - Mathematical logic and foundations
- `5` - Combinatorics
- `11` - Number theory
- `14` - Algebraic geometry
- `54` - General topology
- `60` - Probability theory

Multiple subjects can be specified:
```lean
@[AMS 5 11]  -- Both combinatorics and number theory
theorem erdos_problem : ... := by sorry
```

**In VS Code:** Use `#AMS` command to list all available subjects and their numbers. Hover over a number to see its description.

### The `answer()` Elaborator

For problems that ask questions requiring specific answers (not just yes/no), use `answer(sorry)`:

```lean
/-- Does P hold? -/
@[category research open]
theorem problem_name : answer(sorry) ↔ SomeProperty := by
  sorry
```

When the problem is solved:
- Replace `answer(sorry)` with `answer(True)` or `answer(False)` as appropriate
- Update the category to `research solved` or `research formally solved ...`

**Note:** Providing a term inside `answer()` does NOT automatically mean the problem is mathematically solved - trivial or tautological answers don't count as solutions.

### File Organization

1. **One problem per file** (with flexibility for closely related variants)
2. **Copyright header required** (see template in README.md, use year 2026)
3. **Module docstring** with references:
   ```lean
   /-!
   # Problem Name

   *Reference:* [Title](URL)

   Brief description if needed.
   -/
   ```
4. **Import structure**:
   - Problem files: Import `FormalConjectures.Util.ProblemImports`
   - ForMathlib files: Import only necessary Mathlib modules

### Variants and Related Results

Variants should be in the same file as the main conjecture:

```lean
@[category research open, AMS 11]
theorem main_conjecture : MainStatement := by sorry

@[category research solved, AMS 11]
theorem main_conjecture.variants.weaker_version : WeakerStatement := by sorry

@[category test, AMS 11]
theorem main_conjecture.variants.small_cases : MainStatement with (n < 100) := by
  interval_cases n <;> decide
```

## Lean and Mathlib Style Guidelines

### Naming Conventions

- **Theorems/lemmas/definitions**: `snake_case`
  ```lean
  theorem fermat_last_theorem : ...
  def left_factorial (n : ℕ) := ...
  ```

- **Type classes/structures**: `PascalCase`
  ```lean
  class HasGδSingletons (X : Type*) [TopologicalSpace X] : Prop
  structure MyStructure where
  ```

- **Lemma naming patterns** (follow Mathlib conventions):
  - `add_comm`, `mul_assoc` - operation + property
  - `Nat.factorial_pos` - type + definition + property
  - `foo_of_bar` - derive `foo` from `bar`
  - `bar_iff_foo` - equivalence

### Code Quality

- **Use Unicode math symbols** where appropriate: `∀`, `∃`, `∈`, `⊆`, `∧`, `∨`, `¬`, etc.
- **Format code properly**: Use consistent indentation (2 spaces)
- **Add docstrings** for definitions and main theorems:
  ```lean
  /--
  The left factorial of n: 0! + 1! + 2! + ... + (n-1)!
  -/
  def left_factorial (n : ℕ) := ...
  ```
- **Use `local notation`** for problem-specific notation within namespaces
- **Avoid unnecessary type annotations** when Lean can infer them
- **Use `by` tactic mode** for sorries: `by sorry` (not just `sorry`)

### Imports

- Be specific with imports - don't import more than needed
- In FormalConjecturesForMathlib, import only from Mathlib
- In problem files, import `FormalConjectures.Util.ProblemImports`

## Agent-Specific Requirements

### Before Submitting

**CRITICAL REQUIREMENTS:**

1. **`lake build` MUST pass** without errors before submitting for review
   - Run `lake build` in the repository root
   - Fix all compilation errors
   - Ensure all dependencies are properly imported

2. **`sorry` usage restrictions**:
   - ✅ **ALLOWED**: In `FormalConjectures/` for benchmark problem statements
     ```lean
     @[category research open]
     theorem open_conjecture : Statement := by sorry
     ```
   - ❌ **NOT ALLOWED**: In `FormalConjecturesForMathlib/`
     ```lean
     -- WRONG - will be rejected
     def helper_function : Type := sorry
     lemma helper_lemma : P := by sorry
     ```
   - Exception: `answer(sorry)` is allowed as a placeholder for unknown answers

3. **Completeness**:
   - No placeholder definitions (e.g., `def foo : Type := sorry`)
   - No incomplete type annotations or holes
   - All referenced definitions must exist
   - All imports must be correct

4. **Clean code**:
   - Remove commented-out code
   - Remove debug statements
   - No unused imports
   - No unnecessary intermediate definitions

### Quality Checklist

Before considering your work complete, verify:

- [ ] File has correct copyright header (current year)
- [ ] Module docstring with reference links present
- [ ] Namespace properly opened and closed
- [ ] All theorems have `category` attribute
- [ ] All theorems have at least one `AMS` subject
- [ ] Names follow snake_case convention
- [ ] `lake build` succeeds
- [ ] No `sorry` in FormalConjecturesForMathlib/
- [ ] Docstrings present for main definitions
- [ ] Code properly formatted and readable

### Testing Definitions

When adding new definitions to FormalConjecturesForMathlib/, include basic sanity checks:

```lean
-- In FormalConjecturesForMathlib/Topology/MyDefinition.lean
class MyNewClass (X : Type*) : Prop where
  property : SomeProperty X

-- In FormalConjectures/Paper/ProblemUsingMyDefinition.lean
@[category test]
theorem myNewClass_sanity_check :
    MyNewClass SomeConcreteType := by
  constructor
  exact proof_of_property
```

### Common Pitfalls to Avoid

❌ **DON'T:**
- Use `sorry` outside of problem statement proofs
- Create files without copyright headers
- Forget to add `category` and `AMS` attributes
- Submit code that doesn't compile
- Add large proofs (this is a benchmark repository, not a proof repository)
- Use camelCase for theorem names
- Create placeholder definitions in FormalConjecturesForMathlib/

✅ **DO:**
- Follow existing file patterns in the repository
- Keep formalisations clean and minimal
- Add references to sources
- Use namespaces appropriately
- Test that `lake build` works
- Add variants in the same file as the main problem
- Include basic API for new definitions

## Getting Help

- Check existing files for examples: `FormalConjectures/ErdosProblems/10.lean`, `FormalConjectures/Paper/Kurepa.lean`
- Use `#AMS` command in VS Code to see available subject classifications
- Refer to [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
- See [main README.md](./README.md) for contribution workflow
- See [CONTRIBUTING.md](./CONTRIBUTING.md) for CLA requirements

## Example Template

```lean
/-
Copyright YYYY The Formal Conjectures Authors.
    (Replace YYYY with the current year, e.g., 2026 for work done in 2026)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Problem Name

*Reference:* [Source Title](https://source-url.com)

Brief description if helpful.
-/

namespace ProblemName

/-- Main definition if needed -/
def my_definition (x : ℕ) : ℕ := x + 1

/-- The main conjecture -/
@[category research open, AMS 11]
theorem main_conjecture : SomeStatement := by
  sorry

/-- A variant or special case -/
@[category research solved, AMS 11]
theorem main_conjecture.variants.special_case : WeakerStatement := by
  sorry

end ProblemName
```
