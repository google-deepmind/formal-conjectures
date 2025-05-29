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
# Erdős Problem 868

*Reference:* [erdosproblems.com/868](https://www.erdosproblems.com/868)
-/
open Filter

open scoped Pointwise

/-- A set `A : Set ℕ` is an additive basis of order `o` if every large
enough `n : ℕ` belongs to the o-fold addition of `A`. In other words,
`n` can be written as `n = a₁ + ... + aₒ`, where each `aᵢ ∈ A`. -/
def IsAddBasis (A : Set ℕ) (o : ℕ) : Prop := ∀ᶠ n in atTop, n ∈ o • A

/-- A set `A : Set ℕ` is an additive basis of order `o` if every large
enough `n : ℕ` can be written as `n = a₁ + ... + aₒ`, where each `aᵢ ∈ A`. -/
@[category API, AMS 5, AMS 11]
theorem isAddBasis_iff (A : Set ℕ) (o : ℕ) :
    IsAddBasis A o ↔ ∀ᶠ n in atTop, ∃ (f : Fin o → ℕ) (_ : ∀ i, f i ∈ A), ∑ i, f i = n := by
  have := Set.mem_finset_sum (t := .univ) (f := fun _ : Fin o ↦ A)
  simp_all [IsAddBasis]

/-- A set `A : Set ℕ` is an additive basis of order `2` if every large enough
`n` belongs to `A + A`. -/
@[category API, AMS 5, AMS 11]
theorem isAddBasis_order_two_iff (A : Set ℕ) :
    IsAddBasis A 2 ↔ ∀ᶠ n in atTop, n ∈ A + A := by
  simp [isAddBasis_iff, Set.mem_add, Fin.forall_fin_two]
  refine ⟨fun ⟨a, h⟩ => ⟨a, fun b hb => ?_⟩, fun ⟨a, h⟩ => ⟨a, fun b hb => ?_⟩⟩
  · let ⟨f, hf⟩ := h b hb
    exact ⟨f 0, ⟨hf.1.1, ⟨f 1, ⟨hf.1.2, hf.2⟩⟩⟩⟩
  · let ⟨x, ⟨hx, ⟨y, ⟨hy, hxy⟩⟩⟩⟩ := h b hb
    exact ⟨![x, y], by simp [hx, hy, hxy]⟩

/-- No set is an additive basis of order `0`. -/
@[category API, AMS 5, AMS 11]
theorem not_isAddBasis_zero (A : Set ℕ) : ¬IsAddBasis A 0 := by
  simpa [isAddBasis_iff] using fun n => ⟨n.succ, by simp⟩

/-- A set is an additive basis of order `1` if it contains an infinite tail
of consecutive naturals. -/
@[category API, AMS 5, AMS 11]
theorem isAddBasis_one_iff (A : Set ℕ) :
    IsAddBasis A 1 ↔ ∃ n, Set.Ici n ⊆ A := by
  simp [IsAddBasis, Set.subset_def]

/-- The number of ways in which a natural `n` can be written as the sum of
`o` members of the set `A`. -/
noncomputable
def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

/-- Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which
$n$ can be written as the sum of two elements from $A$. If $f(n)\to\infty$ as $n\to\infty$, then
must $A$ contain a minimal additive basis of order $2$? -/
@[category research open, AMS 5, AMS 11]
theorem erdos_868.parts.i {A : Set ℕ} (hA₁ : IsAddBasis A 2)
    (hA₂ : atTop.Tendsto (fun n => ncard_add_repr A 2 n) atTop) :
    ∃ B ⊆ A, IsAddBasis B 2 ∧ ∀ b ∈ B, ¬IsAddBasis (B \ {b}) 2 :=
  sorry

/-- Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which
$n$ can be written as the sum of two elements from $A$. If $f(n)>\epsilon\log n$ for large $n$
and an arbitrary fixed $\epsilon > 0$, then must $A$ contain a minimal additive
basis of order $2$? -/
@[category research open, AMS 5, AMS 11]
theorem erdos_868.parts.ii {A : Set ℕ} (hA₁ : IsAddBasis A 2) {ε : ℝ} (hε : 0 < ε)
    (hA₂ : ∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) :
    ∃ B ⊆ A, IsAddBasis B 2 ∧ ∀ b ∈ B, ¬IsAddBasis (B \ {b}) 2 := sorry

/-- Erdős and Nathanson proved that this is true if $f(n) > (\log\frac{4}{3})^{-1}\log n$ for
all large $n$. -/
@[category research solved, AMS 5, AMS 11]
theorem erdos_868.variants.fixed_ε {A : Set ℕ} (hA₁ : IsAddBasis A 2)
    (hA₂ : ∀ᶠ (n : ℕ) in atTop, (Real.log (4 / 3))⁻¹ * Real.log n < ncard_add_repr A 2 n) :
    ∃ B ⊆ A, IsAddBasis B 2 ∧ ∀ b ∈ B, ¬IsAddBasis (B \ {b}) 2 := sorry

/-- Härtter and Nathanson proved that there exist additive bases which do not contain
any minimal additive bases. -/
@[category research solved, AMS 5, AMS 11]
theorem erdos_868.variants.Hartter_Nathanson : ∃ A, ∃ o > 1, IsAddBasis A o ∧
    ∀ B ⊆ A, IsAddBasis B o → ∃ b ∈ B, IsAddBasis (B \ {b}) o :=
  sorry
