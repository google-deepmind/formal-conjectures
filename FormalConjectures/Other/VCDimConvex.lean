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

/-! ### What's known in the literature -/

/-- Every convex set in ℝ² has VC dimension at most 3. -/
@[category research solved, AMS 5 52]
lemma vc_lt_four_of_convex_r2 {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    {x : Fin 4 → Fin 2 → ℝ} {y : Set (Fin 4) → Fin 2 → ℝ}
    (hxy : ∀ i s, x i + y s ∈ C ↔ i ∈ s) : False := sorry

/-- There exists a set of infinite VC dimension in ℝ³. -/
@[category research solved, AMS 5 52]
lemma exists_convex_r3_vc_eq_infty :
    ∃ (C : Set (Fin 3 → ℝ)) (hC : Convex ℝ C) (x : ℕ → Fin 3 → ℝ) (y : Set ℕ → Fin 3 → ℝ),
      ∀ i s, x i + y s ∈ C ↔ i ∈ s := sorry

/-! ### What's not in the literature -/

/-- There exists a set of infinite VCₙ dimension in ℝⁿ⁺². -/
@[category research solved, AMS 5 52]
lemma exists_convex_rn_add_two_vc_n_eq_infty (n : ℕ) :
    ∃ (C : Set (Fin (n + 2) → ℝ)) (hC : Convex ℝ C) (x : Fin n → ℕ → Fin (n + 2) → ℝ)
      (y : Set (Fin n → ℕ) → Fin (n + 2) → ℝ),
        ∀ i s, ∑ k, x k (i k) + y s ∈ C ↔ i ∈ s := sorry

/-! ### Conjectures -/

/-- Every convex set in ℝ³ has VC₂ dimension at most 1.

In fact, this set n-shatters an infinite set. -/
@[category research open, AMS 5 52]
lemma vc2_lt_two_of_convex_r3 {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {x y : Fin 2 → Fin 3 → ℝ} {z : Set (Fin 2 × Fin 2) → Fin 3 → ℝ}
    (hxy : ∀ i j s, x i + y j + z s ∈ C ↔ (i, j) ∈ s) : False := sorry

/-- Every convex set in ℝⁿ⁺¹ has VCₙ dimension at most 1. -/
@[category research open, AMS 5 52]
lemma exists_vcn_le_of_convex_rn_add_one (n : ℕ) :
    ∃ d : ℕ, ∀ (C : Set (Fin (n + 1) → ℝ)) (hC : Convex ℝ C) (x : Fin n → ℕ → Fin (n + 1) → ℝ)
      (y : Set (Fin n → ℕ) → Fin (n + 1) → ℝ) (hxy : ∀ i s, ∑ k, x k (i k) + y s ∈ C ↔ i ∈ s),
        False := sorry
