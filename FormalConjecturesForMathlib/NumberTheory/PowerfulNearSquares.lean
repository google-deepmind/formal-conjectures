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

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import FormalConjecturesForMathlib.Data.Nat.Full
public import FormalConjecturesForMathlib.NumberTheory.DiophantineApproximation.Simultaneous

/-!
# Many powerful numbers near a square

For every `k` there is a square `q²` such that `[(q - 1)², (q + 1)²)` contains at least `k`
powerful numbers. Writing `p₁, …, p_k` for the first `k` primes, simultaneous Dirichlet
approximation of the `1 / √(pᵢ³)` gives a `q` and integers `mᵢ` with `mᵢ √(pᵢ³)` within `1/2`
of `q`, so each `mᵢ² pᵢ³` lies in the interval; these numbers are powerful and pairwise distinct
by the parity of the exponent of `pᵢ`.
-/

@[expose] public section

open scoped Finset

namespace Nat

/-- Transfers the real approximation `|y √d - q| < 1/2` to the interval `[(q-1)², (q+1)²)`. -/
theorem exists_sq_mul_mem_Ico_of_abs_lt {q d : ℕ} (hq : 0 < q) (hd : 0 < d) {y : ℤ}
    (h : |(y : ℝ) * Real.sqrt d - q| < 1 / 2) :
    ∃ m : ℕ, 0 < m ∧ (q - 1) ^ 2 ≤ m ^ 2 * d ∧ m ^ 2 * d < (q + 1) ^ 2 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [abs_lt] at h
  have hy : 0 < y := by
    by_contra hc
    push Not at hc
    have : (y : ℝ) ≤ 0 := by exact_mod_cast hc
    nlinarith
  have hc : ((y.toNat : ℕ) : ℝ) = y := by exact_mod_cast Int.toNat_of_nonneg hy.le
  have hr : (((y.toNat ^ 2 * d : ℕ)) : ℝ) = ((y : ℝ) * Real.sqrt d) ^ 2 := by
    push_cast; rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
  refine ⟨y.toNat, by omega, ?_, ?_⟩
  · have hq' : (((q - 1 : ℕ)) : ℝ) = q - 1 := by rw [Nat.cast_sub hq]; simp
    have : (((q - 1) ^ 2 : ℕ) : ℝ) ≤ ((y.toNat ^ 2 * d : ℕ) : ℝ) := by
      rw [hr]; push_cast; rw [hq']; nlinarith
    exact_mod_cast this
  · have : ((y.toNat ^ 2 * d : ℕ) : ℝ) < (((q + 1) ^ 2 : ℕ) : ℝ) := by
      rw [hr]; push_cast
      have h0 : 0 ≤ (y : ℝ) * Real.sqrt d := by nlinarith
      nlinarith
    exact_mod_cast this

/-- For distinct primes `p ≠ p'`, `m² p³ ≠ m'² p'³` (parity of the exponent of `p`). -/
theorem sq_mul_cube_ne {m m' p p' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hp : p.Prime)
    (hp' : p'.Prime) (hne : p ≠ p') : m ^ 2 * p ^ 3 ≠ m' ^ 2 * p' ^ 3 := by
  intro h
  have h1 : (m ^ 2 * p ^ 3).factorization p = (m' ^ 2 * p' ^ 3).factorization p := by rw [h]
  rw [Nat.factorization_mul (by positivity) (pow_ne_zero 3 hp.ne_zero),
    Nat.factorization_mul (by positivity) (pow_ne_zero 3 hp'.ne_zero)] at h1
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization, hp'.factorization, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne] at h1
  omega

/-- For every `k` there is `q ≥ 1` such that `[(q - 1)², q²)` and `[q², (q + 1)²)` together
contain at least `k` powerful numbers. -/
theorem exists_card_powerful_near_sq_ge (k : ℕ) :
    ∃ q : ℕ, 0 < q ∧ k ≤ #((Finset.Ico ((q - 1) ^ 2) (q ^ 2)).filter Powerful) +
      #((Finset.Ico (q ^ 2) ((q + 1) ^ 2)).filter Powerful) := by
  let P : Fin k → ℕ := fun i => Nat.nth Nat.Prime i
  have hP : ∀ i, (P i).Prime := fun i => Nat.prime_nth_prime i
  let d : Fin k → ℕ := fun i => P i ^ 3
  have hd : ∀ i, 0 < d i := fun i => pow_pos (hP i).pos 3
  let S : ℕ := ∑ i, d i
  obtain ⟨q, hq, hy⟩ := Real.exists_pos_forall_abs_mul_sub_int_lt k (2 * (S + 1)) (by omega)
    (fun i => 1 / Real.sqrt (d i))
  have hm : ∀ i, ∃ m : ℕ, 0 < m ∧ (q - 1) ^ 2 ≤ m ^ 2 * d i ∧ m ^ 2 * d i < (q + 1) ^ 2 := by
    intro i
    obtain ⟨y, hyi⟩ := hy i
    apply exists_sq_mul_mem_Ico_of_abs_lt hq (hd i) (y := y)
    have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (by exact_mod_cast hd i)
    have hdS : (d i : ℝ) ≤ S := by
      exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have hsS : Real.sqrt (d i) < S + 1 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    have heq : (y : ℝ) * Real.sqrt (d i) - q =
        -(Real.sqrt (d i) * ((q : ℝ) * (1 / Real.sqrt (d i)) - y)) := by
      field_simp; ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hs]
    calc _ < Real.sqrt (d i) * (1 / ((2 * (S + 1) : ℕ) : ℝ)) := by gcongr
      _ ≤ 1 / 2 := by
        push_cast
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  choose m hm0 hlo hhi using hm
  let g : Fin k → ℕ := fun i => m i ^ 2 * d i
  have hg : Function.Injective g := by
    intro i j hij
    by_contra hne
    exact sq_mul_cube_ne (hm0 i) (hm0 j) (hP i) (hP j)
      (fun h => hne (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h))) hij
  have hsub : Finset.univ.image g ⊆ ((Finset.Ico ((q - 1) ^ 2) (q ^ 2)).filter Powerful) ∪
      ((Finset.Ico (q ^ 2) ((q + 1) ^ 2)).filter Powerful) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    have hpow : Powerful (g i) := (full_pow (m i) le_rfl).mul (full_pow (P i) (by norm_num))
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    by_cases hlt : g i < q ^ 2
    · exact Or.inl ⟨⟨hlo i, hlt⟩, hpow⟩
    · exact Or.inr ⟨⟨by omega, hhi i⟩, hpow⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin] at hc
  exact ⟨q, hq, hc.trans (Finset.card_union_le _ _)⟩

end Nat
