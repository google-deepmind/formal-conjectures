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
# Erdős Problem 170

*Reference:* [erdosproblems.com/170](https://www.erdosproblems.com/170)
-/

open scoped Topology

namespace Erdos170

/-- An `N`-perfect ruler is a subset `A ⊆ ℕ` (the marks), such that each positive integer
`k ≤ N` can be measured, that is, expressed as a difference `k = a₁ - a₀` with `a₁, a₂ ∈ A`. -/
@[reducible]
def PerfectRuler (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ k ∈ Finset.range (N + 1), ∃ᵉ (a₀ ∈ A) (a₁ ∈ A), k = a₁ - a₀

/-- We define the set of all `N`-perfect rulers `A` of length `N`, i.e.
subsets `A ⊆ {0, …, N}`, s.t. `A` is `N`-perfect. -/
def PerfectRulersLengthN (N : ℕ) :
    Finset (Finset ℕ) := (Finset.range (N + 1)).powerset.filter (PerfectRuler N)

/-- The trivial ruler with all marks `{0, …, N}`. -/
abbrev TrivialRuler (N : ℕ) : Finset ℕ := Finset.range (N+1)

/-- Sanity Check: the trivial ruler is actually a perfect ruler if (K ≥ N) -/
@[category API, AMS 05]
lemma trivial_ruler_is_perfect (N : ℕ) : TrivialRuler N ∈ PerfectRulersLengthN N := by
    simp only [PerfectRulersLengthN, Finset.mem_filter, Finset.mem_powerset, Finset.range_subset,
      add_le_add_iff_right]
    exact ⟨by rfl, fun k hk => ⟨0, by simp, k, hk, rfl⟩⟩

/-- We define a function `F N` as the minimum cardinality of an `N`-perfect ruler of length `N`. -/
def F (N : ℕ) : ℕ :=
    Finset.min' (Finset.image Finset.card (PerfectRulersLengthN N))
                (Finset.image_nonempty.mpr ⟨TrivialRuler N, trivial_ruler_is_perfect N⟩)

/-- The problem is to determine the limit of the sequence `(F N) / √N` as `N → ∞`. -/
@[category research open, AMS 05]
lemma erdos170 : Filter.Tendsto (fun N => F N / √N) Filter.atTop (𝓝 answer(sorry)) := sorry
