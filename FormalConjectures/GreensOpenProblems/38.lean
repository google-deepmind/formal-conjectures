/-
Copyright 2026 The Formal Conjectures Authors.

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
# Green's Open Problem 38

*References:*
- [100 open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.38)
- [La79] Lovász, László. "On the Shannon capacity of a graph."
  IEEE Transactions on Information theory 25.1 (1979): 1-7.
- [Po20] Polak, Sven. "New methods in coding theory: Error-correcting codes and the Shannon capacity."
  arXiv preprint arXiv:2005.02945 (2020).
-/

open Filter Set
open scoped Pointwise

namespace Green38

/-- The vector space $\mathbb{F}_7^n$. -/
abbrev 𝔽₇ (n : ℕ) := Fin n → ZMod 7

/-- $A - A$ intersects $\{-1, 0, 1\}^n$ only at $0$. -/
def IntersectsOnlyAtZero {n : ℕ} (A : Finset (𝔽₇ n)) : Prop :=
  ∀ a ∈ A - A, (∀ i, a i ∈ ({-1, 0, 1} : Finset (ZMod 7))) → a = 0

/-- The set of cardinalities of all subsets A where A - A intersects {-1, 0, 1}^n only at 0. -/
def ValidCardinalities (n : ℕ) : Set ℕ :=
  { (A.card) | (A : Finset (𝔽₇ n)) (_ : IntersectsOnlyAtZero A) }

/-- {0, 2, 4} is a valid independent set in C_7, giving cardinality 3. -/
@[category test, AMS 5]
theorem green_38.test_n1_lower :
    3 ∈ ValidCardinalities 1 := by
  refine ⟨{![0], ![2], ![4]}, ?_, by decide⟩
  intro a ha
  simp at ha ⊢
  -- a is a difference of elements from {0, 2, 4}, check all cases
  cases ha
  · norm_num [← List.ofFn_injective.eq_iff]
    decide
  · revert ‹_›
    use by decide+revert ∘ List.mem_cons.1


/--
The largest subset $A \subset \mathbb{F}_7^n$ for which $A - A$ intersects $\{-1, 0, 1\}^n$ only
at $0$.
-/
noncomputable def LargestAdmissibleCardinality : ℕ → ℝ := fun n ↦
  (sSup (ValidCardinalities n) : ℕ)

/-- The lower bound constant $C_1 \approx 3.2578$ from [Po20]. -/
noncomputable def C₁ : ℝ := (367 : ℝ) ^ (5⁻¹ : ℝ)

/-- The upper bound constant $C_2 \approx 3.3177$ from [La79]. -/
noncomputable def C₂ : ℝ := (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7))

/-- Can we improve the lower bound? -/
@[category research open, AMS 05 11]
theorem green_38.lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    ans ≤ᶠ[atTop] LargestAdmissibleCardinality ∧
    ∃ c > C₁, (fun n ↦ c ^ n) =O[atTop] ans := by
  sorry

/-- Can we improve the best upper bound? -/
@[category research open, AMS 05 11]
theorem green_38.upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    LargestAdmissibleCardinality ≤ᶠ[atTop] ans ∧
    ∃ c < C₂, ans =O[atTop] (fun n ↦ c ^ n) := by
  sorry

/--
The current best lower bound is $(C_1 - o(1))^n \leqslant |A|$ where
$C_1 = 367^{1/5} \approx 3.2578$ [Po20, Section 9.1]. -/
@[category research solved, AMS 05 11]
theorem green_38.variants.best_lower :
    ∀ ε > 0, ∀ᶠ n in atTop, (C₁ - ε) ^ n ≤ LargestAdmissibleCardinality n := by
  sorry

/-- The current best upper bound is $|A| \leqslant (C_2 + o(1))^n$ where
$C_2 = \frac{7 \cos(\pi/7)}{1 + \cos(\pi/7)} \approx 3.3177$ [La79, Corollary 5]. -/
@[category research solved, AMS 05 11]
theorem green_38.variants.best_upper :
    ∀ ε > 0, ∀ᶠ n in atTop, LargestAdmissibleCardinality n ≤ (C₂ + ε) ^ n := by
  sorry

/-- 0 is a valid cardinality, since the empty set vacuously satisfies the condition. -/
@[category test, AMS 05 11]
theorem green_38.test_zero_mem_validCardinalities {n : ℕ} :
    0 ∈ ValidCardinalities n := by
  use ∅
  simp [IntersectsOnlyAtZero]

/-- The set of valid cardinalities we take the supremum over is bounded above. -/
@[category test, AMS 05 11]
theorem green_38.test_bound_above {n : ℕ} :
    BddAbove (ValidCardinalities n) := by
  use 7 ^ n
  rintro _ ⟨A, _, rfl⟩
  calc A.card
    _ ≤ Fintype.card (𝔽₇ n) := A.card_le_univ
    _ = _ := by simp

end Green38
