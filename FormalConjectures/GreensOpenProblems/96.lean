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
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.MetricSpace.Basic

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

open MeasureTheory Filter Topology

namespace Green96

/-!
## Definitions

The following definitions formalize the harmonic analysis concepts needed for this problem.
Note that some underlying theory (particularly for sets of analyticity) may need further
development in mathlib.
-/

/-- The space c₀(Λ) of sequences indexed by Λ that converge to zero.
This is formalized as functions from Λ to ℂ that tend to zero at infinity,
equipped with the supremum norm. -/
def c0Space (Λ : Set ℤ) : Type :=
  {f : Λ → ℂ // Tendsto (fun n : Λ => ‖f n‖) cofinite (𝓝 0)}

/-- The Fourier algebra A(Λ) for Λ ⊂ ℤ.
This should consist of restrictions to Λ of Fourier transforms of L¹ functions on the circle.
For now, we define it as the space of functions on Λ that arise as Fourier coefficients
of L¹ functions on the unit circle.

TODO: This needs proper formalization with the full Fourier algebra structure. -/
def FourierAlgebra (Λ : Set ℤ) : Type :=
  {f : Λ → ℂ // ∃ (g : AddCircle 1 → ℂ), Integrable g ∧
    ∀ n : Λ, f n = ∫ x, g x * conj (fourier (n : ℤ) x) ∂haarAddCircle}

/-- A set Λ ⊂ ℤ is a Sidon set in the harmonic analysis sense if the
Fourier algebra A(Λ) coincides with c₀(Λ).

This means every sequence in c₀(Λ) can be realized as Fourier coefficients
of some L¹ function on the circle. -/
def IsSidonHA (Λ : Set ℤ) : Prop :=
  ∀ f : c0Space Λ, ∃ g : AddCircle 1 → ℂ, Integrable g ∧
    ∀ n : Λ, f.val n = ∫ x, g x * conj (fourier (n : ℤ) x) ∂haarAddCircle

/-- A set Λ ⊂ ℤ is a set of analyticity if only analytic functions act on A(Λ).

TODO: This definition is a placeholder. The proper formalization requires:
1. Defining what it means for a function to "act" on the Fourier algebra
2. Formalizing the notion of analytic functions in this context
3. Characterizing when only analytic functions have this property

For now, we use a placeholder that captures the idea that the algebra has
special analytic properties. -/
def IsSetOfAnalyticity (Λ : Set ℤ) : Prop :=
  -- Placeholder: A set is of analyticity if it's not Sidon and satisfies
  -- certain analytic conditions. The proper definition requires substantial
  -- development of harmonic analysis theory.
  ¬IsSidonHA Λ ∧ ∃ (property : (Λ → ℂ) → Prop), True
  -- TODO: Replace with proper characterization of sets of analyticity

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
