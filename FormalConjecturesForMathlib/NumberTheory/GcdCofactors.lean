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

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Cofactors `a / (a, b)` of a finite set

For a finite set `A ⊆ ℕ`, consider the set of cofactors `a / gcd a b` with `a, b ∈ A`.
Erdős and Szemerédi observed that there are at least `√|A|` of them: fixing a positive `a ∈ A`,
the map `b ↦ (a / (a, b), b / (a, b))` is injective. The set `{1, 2, …, 2^(n-1)}` shows that
`n` cofactors may be all one gets.
-/

@[expose] public section

open scoped Finset

namespace Nat

/-- Fixing a positive `a ∈ A`, the map `b ↦ (a / (a, b), b / (a, b))` is injective, so `|A|` is
at most the square of the number of cofactors. -/
theorem card_le_sq_card_image_div_gcd (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) (hpos : 0 < a) :
    #A ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) ^ 2 := by
  set D := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b with hD
  have hmem : ∀ x ∈ A, ∀ y ∈ A, x / x.gcd y ∈ D := fun x hx y hy =>
    Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  let f : ℕ → ℕ × ℕ := fun b ↦ (a / a.gcd b, b / b.gcd a)
  have hmaps : ∀ b ∈ A, f b ∈ D ×ˢ D := fun b hb =>
    Finset.mem_product.2 ⟨hmem a ha b hb, hmem b hb a ha⟩
  have hinj : Set.InjOn f A := by
    intro b _ c _ hbc
    simp only [f, Prod.mk.injEq] at hbc
    obtain ⟨h1, h2⟩ := hbc
    have hg : a.gcd b = a.gcd c := by
      rw [← Nat.div_div_self (Nat.gcd_dvd_left a b) hpos.ne',
        ← Nat.div_div_self (Nat.gcd_dvd_left a c) hpos.ne', h1]
    rw [Nat.gcd_comm b a, Nat.gcd_comm c a, hg] at h2
    rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right a b), hg, h2,
      Nat.div_mul_cancel (Nat.gcd_dvd_right a c)]
  calc #A ≤ #(D ×ˢ D) := Finset.card_le_card_of_injOn f hmaps hinj
    _ = #D ^ 2 := by rw [Finset.card_product, sq]

/-- Erdős–Szemerédi: a finite set `A ⊆ ℕ` has at least `⌊√|A|⌋` cofactors `a / (a, b)`. -/
theorem sqrt_card_le_card_image_div_gcd (A : Finset ℕ) :
    Nat.sqrt #A ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) := by
  by_cases h : ∃ a ∈ A, 0 < a
  · obtain ⟨a, ha, hpos⟩ := h
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1
      ((Nat.sqrt_le' #A).trans (card_le_sq_card_image_div_gcd A ha hpos))
  · simp only [not_exists, not_and, not_lt] at h
    have hsub : A ⊆ {0} := fun x hx => by simpa using Nat.le_zero.1 (h x hx)
    have hn : #A ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    refine (Nat.sqrt_le_self _).trans ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < #A)
      rw [h1]
      exact Finset.card_pos.2 ⟨x / x.gcd x,
        Finset.mem_image.2 ⟨(x, x), Finset.mem_product.2 ⟨hx, hx⟩, rfl⟩⟩

/-- For every `n` some set of size `n` (namely `{1, 2, …, 2^(n-1)}`) has at most `n` cofactors. -/
theorem exists_card_eq_card_image_div_gcd_le (n : ℕ) :
    ∃ A : Finset ℕ, #A = n ∧ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) ≤ n := by
  set A := (Finset.range n).image (2 ^ ·) with hA
  have hcard : #A = n := by
    rw [hA, Finset.card_image_of_injective _ (Nat.pow_right_injective le_rfl),
      Finset.card_range]
  refine ⟨A, hcard, hcard ▸ Finset.card_le_card ?_⟩
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.1 hd
  obtain ⟨hx, -⟩ := Finset.mem_product.1 hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  have hdvd : 2 ^ i / (2 ^ i).gcd y ∣ 2 ^ i := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  show 2 ^ i / (2 ^ i).gcd y ∈ A
  rw [hk']
  exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (lt_of_le_of_lt hk (Finset.mem_range.1 hi)),
    rfl⟩

end Nat
