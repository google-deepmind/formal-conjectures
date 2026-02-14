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
  - `OptimizationConstants/` - Problems from [Tao's Optimization Constants](https://teorth.github.io/optimizationproblems/)
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
theorem main_conjecture : ... := by
  sorry

theorem main_conjecture.variants.special_case : ... := by
  sorry
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
theorem riemann_hypothesis : ... := by
  sorry

@[category test, AMS 11]
theorem sanity_check : ¬ SomeBadProperty := by
  sorry

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
theorem erdos_problem : ... := by
  sorry
```

**In VS Code:** Use `#AMS` command to list all available subjects and their numbers. Hover over a number to see its description.

Full list of AMS subjects
| Code | Name | Keywords |
|------|------|----------|
| 00 | General and overarching topics | general |
| 03 | Mathematical logic and foundations | logic, set theory, model theory |
| 05 | Combinatorics | combinatorics, graph theory, enumeration |
| 06 | Order | order, lattice, poset, partial order |
| 08 | General algebraic systems | universal algebra, algebraic system |
| 11 | Number theory | number theory, prime, arithmetic, diophantine |
| 12 | Field theory and polynomials | field, polynomial, galois |
| 13 | Commutative algebra | commutative, ring, ideal, module |
| 14 | Algebraic geometry | algebraic geometry, variety, scheme |
| 15 | Linear algebra | linear algebra, matrix, vector |
| 16 | Associative rings and algebras | associative, ring, algebra |
| 17 | Nonassociative rings and algebras | lie algebra, jordan |
| 18 | Category theory; homological algebra | category, functor, homological |
| 19 | K-theory | k-theory |
| 20 | Group theory and generalizations | group, finite group, representation |
| 22 | Topological groups + Lie groups | topological group, lie group |
| 26 | Real functions | real analysis, real function, derivative |
| 28 | Measure and integration | measure, integration, lebesgue |
| 30 | Functions of a complex variable | complex analysis, holomorphic, analytic |
| 31 | Potential theory | potential, harmonic function, subharmonic |
| 32 | Complex analysis | several complex variables, complex manifold |
| 33 | Special functions | special function, gamma, zeta, bessel |
| 34 | Ordinary differential equations | ode, differential equation |
| 35 | Partial differential equations | pde, partial differential |
| 37 | Dynamical systems and ergodic theory | dynamical, ergodic, chaos |
| 39 | Difference and functional equations | difference equation, functional equation |
| 40 | Sequences + series + summability | sequence, series, convergence |
| 41 | Approximations and expansions | approximation, expansion, interpolation |
| 42 | Harmonic analysis on Euclidean spaces | harmonic analysis, fourier |
| 43 | Abstract harmonic analysis | abstract harmonic |
| 44 | Integral transforms + operational calculus | integral transform, laplace |
| 45 | Integral equations | integral equation |
| 46 | Functional analysis | functional analysis, banach, hilbert |
| 47 | Operator theory | operator, spectral |
| 49 | Calc. of vars. and opt. ctrl.; optimiz. | calculus of variations, optimal control |
| 51 | Geometry | geometry, euclidean, projective |
| 52 | Convex and discrete geometry | convex, polytope, discrete geometry |
| 53 | Differential geometry | differential geometry, manifold, riemannian |
| 54 | General topology | topology, topological space, compact |
| 55 | Algebraic topology | algebraic topology, homotopy, homology |
| 57 | Manifolds and cell complexes | manifold, cell complex |
| 58 | Global analysis + analysis on manifolds | global analysis |
| 60 | Probability theory | probability, stochastic, random |
| 62 | Statistics | statistics, estimation, hypothesis |
| 65 | Numerical analysis | numerical, approximation, algorithm |
| 68 | Computer science | computer science, complexity, algorithm |
| 70 | Mechanics of particles and systems | mechanics, particle, celestial |
| 74 | Mechanics of deformable solids | elasticity, solid mechanics |
| 76 | Fluid mechanics | fluid, navier-stokes |
| 78 | Optics + electromagnetic theory | optics, electromagnetic |
| 80 | Classical thermodynamics + heat transfer | thermodynamics, heat |
| 81 | Quantum theory | quantum, quantum mechanics |
| 82 | Statistical mechanics | statistical mechanics |
| 83 | Relativity and gravitational theory | relativity, gravity, einstein |
| 85 | Astronomy and astrophysics | astronomy, astrophysics |
| 86 | Geophysics | geophysics |
| 90 | Mathematical programming | optimization, linear programming |
| 91 | Game theory | game theory, economics |
| 92 | Biology and other natural sciences | biology, mathematical biology |
| 93 | Systems theory; control | control theory, systems theory |
| 94 | Information and communication + circuits | information theory, coding theory |
| 97 | Mathematics education | education |

### The `answer()` Elaborator

For problems that ask questions requiring specific answers (not just yes/no), use `answer(sorry)`:

```lean
/-- Does $P$ hold? -/
@[category research open]
theorem problem_name : answer(sorry) ↔ SomeProperty := by
  sorry
```

Note that if the statement of the theorem depends on some variables, then the quantification should
happen *after* the `answer(sorry)`, i.e.
```lean
/-- Does $P(n)$ hold for all $n$? -/
@[category research open]
theorem problem_name : answer(sorry) ↔ ∀ n, P n := by
  sorry
```
rather than
```lean
/-- Does $P(n)$ hold for all $n$? -/
@[category research open]
theorem problem_name (n) : answer(sorry) ↔ P n := by
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
5. If a problem fits in several directories then it should stated in one directory rather than copied
   accross several. In other directories, one can simply add a file with a declaration pointing
   to the original, e.g.
   ```lean
   @[category research open, AMS 11]
   theorem pointer_to_original : type_of% my_original_theorem := by
     sorry
   ```
   See for example `FormalConjectures/GreensOpenProblems/81.lean`.

### Variants and Related Results

Variants should be in the same file as the main conjecture:

```lean
@[category research open, AMS 11]
theorem main_conjecture : MainStatement := by
  sorry

@[category research solved, AMS 11]
theorem main_conjecture.variants.weaker_version : WeakerStatement := by
  sorry

@[category test, AMS 11]
theorem main_conjecture.variants.small_cases : MainStatement with (n < 100) := by
  interval_cases n <;> decide
```

## Lean and Mathlib Style Guidelines

### Naming Conventions

Follow [Mathlib's naming conventions](https://leanprover-community.github.io/contribute/naming.html). Unlike Lean 3, Lean 4 uses a combination of `snake_case`, `lowerCamelCase`, and `UpperCamelCase`:

#### Capitalization Rules

1. **Terms of Props** (proofs, theorem names) use `snake_case`:
   ```lean
   theorem fermat_last_theorem : FermatLastTheorem := by sorry
   lemma add_comm (a b : ℕ) : a + b = b + a := by sorry
   ```

2. **Props and Types** (inductive types, structures, classes) use `UpperCamelCase`:
   ```lean
   class HasGδSingletons (X : Type*) [TopologicalSpace X] : Prop
   structure MyStructure where
     field1 : ℕ
     field2 : String
   inductive Color where
     | Red | Green | Blue
   ```

3. **Functions** are named the same way as their return values:
   - A function `A → B → C` is named as though it's a term of type `C`
   - If `C` is a `Prop`, use `snake_case`
   - If `C` is a `Type`, use `lowerCamelCase`

4. **All other terms of Types** use `lowerCamelCase`:
   ```lean
   def leftFactorial (n : ℕ) : ℕ := ∑ i in Finset.range n, i!
   def myFunction (x : ℕ) : ℕ := x + 1
   ```

5. **UpperCamelCase in snake_case contexts**: When something named with `UpperCamelCase` is part of something named with `snake_case`, it is referenced in `lowerCamelCase`:
   ```lean
   theorem fermat_last_theorem : FermatLastTheorem := by sorry
   theorem nat_factorial_pos (n : ℕ) : 0 < n! := by sorry
   ```

6. **Acronyms**: Written as a group in upper-/lowercase depending on the first character:
   - `LE`, `LT`, `GE`, `GT` (when in `UpperCamelCase` context)
   - `le`, `lt`, `ge`, `gt` (when in `lowerCamelCase` context)

7. **Structure fields and constructors**: Follow the same rules (1-6) as top-level declarations

#### Common Naming Patterns

- `add_comm`, `mul_assoc` - operation + property
- `Nat.factorial_pos` - namespace + definition + property
- `foo_of_bar` - derive `foo` from hypothesis `bar`
- `bar_iff_foo` - equivalence between `bar` and `foo`
- `foo_le_bar` - inequality statement

#### Exceptions

Some rare exceptions exist for consistency:
- `Ne` (not `NE`) follows `Eq`
- Intervals: `Set.Icc`, `Set.Iic` (capital `I` despite convention)
- Some legacy structure fields may be lowercase

**Note**: In this repository, most declarations are theorems (terms of Props), so you'll primarily use `snake_case`.

### Code Quality

- **Use Unicode math symbols** where appropriate: `∀`, `∃`, `∈`, `⊆`, `∧`, `∨`, `¬`, etc.
- **Format code properly**: Use consistent indentation (2 spaces)
- **Add docstrings** with the math written in Latex for definitions and main theorems:
  ```lean
  /--
  The left factorial of $n$, defined as $0! + 1! + 2! + ... + (n-1)!$
  -/
  def left_factorial (n : ℕ) := ...
  ```
- **Use `local notation`** for problem-specific notation within namespaces
- **Avoid unnecessary type annotations** when Lean can infer them
- **Use `by` tactic mode** for sorries: `by sorry` (not just `sorry`)
- **Do not try to add a suggested informal proof for an open research problem**
- **Avoid using tactics like `native_decide` in proofs**. These are completely banned in `FormalConjecturesForMathlib`
  and may be considered on a case by case basis for in `category test` statements in problem files
  when the goal is a large computation.

### Imports

- Be specific with imports - don't import more than needed
- In FormalConjecturesForMathlib, import only from Mathlib
- In problem files, import only `FormalConjectures.Util.ProblemImports`, unless you are adding a
   pointer to another problem or need to state an implication.

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
- Add references to sources. These should all appear in the module docstring reference list, and
  ideally each conjecture statement docstring should have a reference.
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
def myDefinition (x : ℕ) : ℕ := x + 1

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
