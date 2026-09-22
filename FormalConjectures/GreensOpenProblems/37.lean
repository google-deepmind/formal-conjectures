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
# Ben Green's Open Problem 37

What is the smallest subset of `ℕ` containing, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`?

*References:*
- [Ben Green's Open Problem 37](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.37)
- [Green & Tao, *The primes contain arbitrarily long arithmetic progressions* (arXiv:math/0404188)](https://arxiv.org/abs/math/0404188)
-/

@[expose] public section

namespace Green37

open Set Filter
open scoped Asymptotics

/-- `A` contains an arithmetic progression of length `k` and common difference `d` for every `d ∈ {1, …, N}`. -/
def IsAPCover (A : Set ℕ) (N k : ℕ) : Prop := ∀ d, 1 ≤ d ∧ d ≤ N → Set.ContainsAP A k d

/-- The minimum size of a subset of `ℕ` that contains, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`. -/
noncomputable def m (N k : ℕ) : ℕ :=
  sInf { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k }

/--
Given a natural number `N`, what is the smallest size of a subset of `ℕ` that contains, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`.
-/
@[category research open, AMS 5 11]
theorem green_37 (N k : ℕ) :
    IsLeast { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k }
      ((answer(sorry) : ℕ → ℕ → ℕ) N k) := by
  sorry

/--
Asymptotic version: determine the asymptotic behavior of `m(N, k)` as `N` grows.
The solver should determine a function `f : ℕ → ℕ → ℝ` such that, for each `k`,
`f k` eventually equals `(fun N ↦ (m N k : ℝ))`.
-/
@[category research open, AMS 5 11]
theorem green_37_asymptotic (k : ℕ) :
    ∀ᶠ N in atTop, (m N k : ℝ) = (answer(sorry) : ℕ → ℕ → ℝ) k N := by
  sorry

/-- Determine, for each `k`, the asymptotic equivalence class (theta) of `m(N, k)` as `N` grows. -/
@[category research open, AMS 5 11]
theorem green_37_theta (k : ℕ) :
    (fun N ↦ (m N k : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℕ → ℝ) k := by
  sorry

/-- The interval `{0, …, kN}` contains, for each `d = 1, …, N`, the arithmetic progression
`{0, d, …, (k - 1)d}`, so `m(N, k) ≤ kN + 1`. -/
@[category API, AMS 5 11]
theorem m_le_mul_add_one (N k : ℕ) : m N k ≤ k * N + 1 := by
  apply Nat.sInf_le
  refine ⟨Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

/--
Writing `F_k(N)` for `m(N, k)`, Green conjectures that `F_k(N) ≫_k N^(1 - c_k)` for some
sequence `c_k` with `c_k → 0` as `k → ∞`.
-/
@[category research open, AMS 5 11]
theorem green_37_lower_bound :
    ∃ c : ℕ → ℝ, Tendsto c atTop (nhds 0) ∧
      ∀ k, 0 < k → (fun N : ℕ ↦ (N : ℝ) ^ (1 - c k)) =O[atTop] fun N ↦ (m N k : ℝ) := by
  sorry

end Green37
