/-
Copyright 2025 The Formal Conjectures Authors.

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
# Ben Green's Open Problem 96 (The Dichotomy Problem)

Is every set Λ ⊂ ℤ either a Sidon set (in the harmonic analysis sense), or a set of
analyticity?

This problem was raised in the 1960s in commutative harmonic analysis. Jean Bourgain
considered it a "beautiful open question" but noted the subject had largely fallen out
of fashion.

**Note:** This is different from the combinatorial notion of Sidon sets (where pairwise
sums are distinct), which is defined in `FormalConjecturesForMathlib.Combinatorics.Basic`.

## References
 - [Ben Green's Open Problem 96](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.96)
 - Kahane and Katznelson [170]: Showed that random sets are almost surely Sidon or
   almost surely sets of analyticity depending on the probability distribution.
-/

namespace Green96

/-!
## TODO: Definitions needed

The following definitions are placeholders and need to be properly formalized in mathlib
or FormalConjecturesForMathlib:

1. **Fourier Algebra A(Λ)**: For a set Λ ⊂ ℤ, the Fourier algebra A(Λ) should be defined
   as {(f̂(λ))_{λ ∈ Λ} : f ∈ L¹(𝕋)}, where f̂ denotes the Fourier transform.

2. **Space c₀(Λ)**: The space of sequences indexed by Λ that tend to zero, equipped with
   the supremum norm.

3. **Sidon Set (Harmonic Analysis)**: A set Λ is Sidon (in the harmonic analysis sense)
   if A(Λ) = c₀(Λ).

4. **Set of Analyticity**: A set Λ is a set of analyticity if only analytic functions F
   act on A(Λ).

These concepts require substantial development of harmonic analysis theory in mathlib.
-/

/-- Placeholder: A set Λ ⊂ ℤ is a Sidon set in the harmonic analysis sense if the
Fourier algebra A(Λ) coincides with c₀(Λ), the algebra of sequences tending to zero.

TODO: This needs proper formalization with the Fourier algebra and c₀ space. -/
def IsSidonHA (Λ : Set ℤ) : Prop :=
  sorry

/-- Placeholder: A set Λ ⊂ ℤ is a set of analyticity if only analytic functions F act
on the Fourier algebra A(Λ).

TODO: This needs proper formalization with the Fourier algebra and analytic functions
acting on it. -/
def IsSetOfAnalyticity (Λ : Set ℤ) : Prop :=
  sorry

/--
**The Dichotomy Problem (Problem 96):**

Is every set Λ ⊂ ℤ either a Sidon set (in the harmonic analysis sense), or a set of
analyticity?

This conjecture asks whether subsets of integers must satisfy one of two specific
properties in harmonic analysis. The problem connects to the work of Kahane, Katznelson,
Pisier, and Jean Bourgain.

**Related Results:**
- Kahane and Katznelson showed that a random set Λ with ℙ(n ∈ Λ) = pₙ is almost surely
  Sidon if npₙ is bounded, and almost surely a set of analyticity if npₙ → ∞.
- Pisier showed that S ⊂ ℤ is Sidon if and only if it has property (⋆): there exists
  δ > 0 such that any finite subset S' ⊂ S contains an independent set A with
  |A| ≥ δ|S'|.
-/
@[category research open, AMS 11]
theorem green_96 : answer(sorry) ↔ ∀ Λ : Set ℤ, IsSidonHA Λ ∨ IsSetOfAnalyticity Λ := by
  sorry

end Green96
