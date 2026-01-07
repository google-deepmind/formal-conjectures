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
# VCₙ dimension of convex sets in ℝⁿ, ℝⁿ⁺¹, ℝⁿ⁺²

In the literature it is known that every convex set in ℝ² has VC dimension at most 3,
and there exists a convex set in ℝ³ with infinite VC dimension (even more strongly,
which shatters an infinite set).

This file states that every convex set in ℝⁿ has finite VCₙ dimension, constructs a convex set in
ℝⁿ⁺² with infinite VCₙ dimension (even more strongly, which n-shatters an infinite set),
and conjectures that every convex set in ℝⁿ⁺¹ has finite VCₙ dimension.
-/

open scoped EuclideanGeometry Pointwise

/-! ### What's known in the literature -/

/-- Every convex set in ℝ² has VC dimension at most 3. -/
@[category research solved, AMS 5 52]
lemma hasAddVCDimAtMost_three_of_convex_r2 {C : Set ℝ²} (hC : Convex ℝ C) : HasAddVCDimAtMost C 3 :=
  sorry

/-- There exists a set in ℝ³ shattering an infinite set. -/
@[category research solved, AMS 5 52]
lemma exists_infinite_convex_r3_shatters :
    ∃ A C : Set ℝ³, A.Infinite ∧ Convex ℝ C ∧ Shatters {t +ᵥ C | t : ℝ³} A := sorry

/-! ### What's not in the literature -/

/-- There exists a set of infinite VCₙ dimension in ℝⁿ⁺². -/
@[category research solved, AMS 5 52]
lemma exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost (n : ℕ) :
    ∃ C : Set (Fin (n + 2) → ℝ), Convex ℝ C ∧ ∀ d, ¬ HasAddVCNDimAtMost C n d := sorry

/-! ### Conjectures -/

/-- Every convex set in ℝ³ has VC₂ dimension at most 1. -/
@[category research open, AMS 5 52]
lemma hasAddVCNDimAtMost_two_one_of_convex_r3 {C : Set ℝ³} (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 1 := sorry

/-- For every `n` there exists some `d` such that every convex set in ℝⁿ⁺¹ has VCₙ dimension at
most `d`. -/
@[category research open, AMS 5 52]
lemma exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one (n : ℕ) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d := sorry

/-- If `n ≥ 2`, every convex set in ℝⁿ⁺¹ has VCₙ dimension at most 1. -/
@[category research open, AMS 5 52]
lemma hasAddVCNDimAtMost_n_one_of_convex_rn_add_one {n : ℕ} (hn : 2 ≤ n) {C : Set (Fin (n + 1) → ℝ)}
    (hC : Convex ℝ C) : HasAddVCNDimAtMost C n 1 := sorry
