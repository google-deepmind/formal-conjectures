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
module

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 94

*Reference:*
- [Ben Green's Open Problem 94](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.94)
- [erdosproblems.com/120](https://www.erdosproblems.com/120)
- [OAI26a] OpenAI, *The dyadic case of the Erdős similarity conjecture*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026/paper.pdf
-/

@[expose] public section

open Set MeasureTheory

namespace Green94

set_option linter.style.formal_proof_palomar false in
/--
Let `A ⊂ R` be a set of positive outer measure. Does $A$ contain an affine copy of `{1, 1/2, 1/4, . . . }`?

The answer is "no".
-/
@[category research solved, question, AMS 28, formal_proof using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/153d79d6c82c76fe1bee860742af800840c974d9/FormalConjectures/GreensOpenProblems/94.lean#L174"]
theorem green_94_outer_measure :
   ¬ ∀ A : Set ℝ,
   volume A > 0 →
   ∃ a b : ℝ, a ≠ 0 ∧ ∀ n : ℕ, a * (1 / 2^n) + b ∈ A := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let `A ⊂ R` be a set of positive measure. Does $A$ contain an affine copy of `{1, 1/2, 1/4, . . . }`?

The answer is "no": there are compact sets of measure arbitrarily close to $1$ in $[0, 1]$
that contain no affine copy of $\{2^{-n} : n \geq 1\}$. This was proved by an internal OpenAI
model in September 2026 [OAI26a]; see the linked Lean proof. The linked statement is
`green_94.variants.dyadic_affine_avoidance`; see `green_94_of_dyadic_affine_avoidance`.
-/
@[category research solved, question, AMS 28, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/DyadicAvoidance/Main.lean#L103"]
theorem green_94 :
   ¬ ∀ A : Set ℝ,
   MeasurableSet A ∧ volume A > 0 →
   ∃ a b : ℝ, a ≠ 0 ∧ ∀ n : ℕ, a * (1 / 2^n) + b ∈ A := by
  sorry

/--
The statement of the linked Lean proof, with its definition of the dyadic points unfolded: for
every `0 < η < 1` there is a compact `E ⊆ [0, 1]` of measure greater than `1 - η` such that
every affine copy `x + s 2^{-n}`, `s ≠ 0`, of $\{2^{-n} : n \geq 1\}$ has a point outside `E`.
-/
@[category research solved, AMS 28]
theorem green_94.variants.dyadic_affine_avoidance :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * (2 : ℝ)⁻¹ ^ n ∉ E := by
  sorry

/-- The case `η = 1 / 2` of [OAI26a] answers `green_94`: a compact set is measurable. -/
@[category test, AMS 28]
theorem green_94_of_dyadic_affine_avoidance
    (h : type_of% green_94.variants.dyadic_affine_avoidance) : type_of% green_94 := by
  intro hall
  obtain ⟨E, -, hE, hvol, havoid⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨a, b, ha, hab⟩ := hall E ⟨hE.measurableSet, pos_of_gt hvol⟩
  obtain ⟨n, -, hn⟩ := havoid b a ha
  apply hn
  have : b + a * (2 : ℝ)⁻¹ ^ n = a * (1 / 2 ^ n) + b := by
    rw [inv_pow, one_div]
    ring
  rw [this]
  exact hab n

end Green94
