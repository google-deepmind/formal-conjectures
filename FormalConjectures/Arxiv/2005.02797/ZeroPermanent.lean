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
# The zero permanent of a random sign matrix

* V. H. Vu, *Recent progress in combinatorial random matrix theory*,
  [Conjecture 6.12](https://arxiv.org/pdf/2005.02797#page=11).
* Z. Hunter, M. Kwan and L. Sauermann, *Exponential anticoncentration of the permanent*,
  [Theorem 1.1 and §1.4](https://arxiv.org/html/2509.22577#S1).
* I. M. Wanless, *Permanents of matrices of signed ones*,
  [Theorem 1](https://users.monash.edu.au/~iwanless/papers/wangconjLAMA.pdf#page=6),
  gives Teichert's characterization of the orders admitting a zero permanent.
-/

@[expose] public section

namespace Arxiv.«2005.02797»

open Filter
open scoped Topology NNRat

/-- The integer permanent of a square sign matrix, with true representing $+1$. -/
def signPermanent {n : ℕ} (a : Fin n → Fin n → Bool) : ℤ :=
  (Matrix.of fun i j ↦ if a i j then (1 : ℤ) else -1).permanent

/-- The exact probability of permanent $x$ under independent uniform signs in every entry. -/
def permanentProbability (n : ℕ) (x : ℤ) : ℚ≥0 :=
  (Finset.univ.filter fun a : Fin n → Fin n → Bool ↦ signPermanent a = x).dens

/-- Vu's Conjecture 6.12. The probability that a random sign matrix has zero permanent
eventually decays faster than every exponential $e^{-cn}$, $c>0$. -/
@[category research open, AMS 15 60]
theorem vu_permanent : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    (permanentProbability n 0 : ℝ) ≤ Real.exp (-c * n) := by
  sorry

/-- Hunter, Kwan and Sauermann's exponential bound holds with one absolute rate for every
matrix order and every possible value of the permanent. -/
@[category research solved, AMS 15 60]
theorem vu_permanent.variants.exponential : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ x : ℤ,
    (permanentProbability n x : ℝ) ≤ Real.exp (-c * n) := by
  sorry

/-- Teichert's characterization. The zero-permanent probability vanishes exactly when
$n+1$ is a power of two. -/
@[category research solved, AMS 5 15]
theorem vu_permanent.variants.zero_probability_iff {n : ℕ} (hn : 0 < n) :
    permanentProbability n 0 = 0 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  sorry

/-- Positive mass is equivalent to the existence of a sign matrix with the specified permanent. -/
@[category API, AMS 15 60]
theorem permanentProbability_pos_iff (n : ℕ) (x : ℤ) :
    0 < permanentProbability n x ↔ ∃ a : Fin n → Fin n → Bool, signPermanent a = x := by
  simp [permanentProbability, Finset.dens_pos, Finset.filter_nonempty_iff]

/-- In order two, eight of the sixteen sign matrices have zero permanent. -/
@[category API, AMS 15 60]
theorem permanentProbability_two : permanentProbability 2 0 = 1 / 2 := by
  have h : (Finset.univ.filter fun a : Fin 2 → Fin 2 → Bool ↦ signPermanent a = 0).card = 8 := by
    decide
  norm_num [permanentProbability, Finset.dens, h, Fintype.card_pi]

/-- A single matrix supplies probability at least $2^{-n^2}$ to its permanent value. -/
@[category API, AMS 15 60]
theorem single_matrix_lower_bound {n : ℕ} (a : Fin n → Fin n → Bool) :
    ((2 : ℚ≥0) ^ (n ^ 2))⁻¹ ≤ permanentProbability n (signPermanent a) := by
  have h : ({a} : Finset _).dens ≤ permanentProbability n (signPermanent a) :=
    Finset.dens_le_dens (Finset.singleton_subset_iff.mpr (by simp))
  simpa [Fintype.card_pi, ← pow_mul, sq] using h

/-- With every column except the first equal to $+1$, the permanent is $n!$ times the
sum of the signs in the first column of an order $n+1$ matrix. -/
@[category API, AMS 5 15]
theorem signPermanent_first_column {n : ℕ} (v : Fin (n + 1) → Bool) :
    signPermanent (fun i j ↦ if j = 0 then v i else true) =
      (n.factorial : ℤ) * ∑ i, (if v i then (1 : ℤ) else -1) := by
  let f (i : Fin (n + 1)) : ℤ := if v i then 1 else -1
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)), f (σ 0) := by
      simp [signPermanent, Matrix.permanent, Fin.prod_univ_succ, f]
    _ = ∑ z : Fin (n + 1) × Equiv.Perm (Fin n), f z.1 := by
      symm
      apply Fintype.sum_equiv Equiv.Perm.decomposeFin.symm
      rintro ⟨i, σ⟩
      simp
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      rfl

/-- In every positive even order, balancing the signs in the first column gives an explicit
lower bound for the zero-permanent probability. -/
@[category API, AMS 5 15 60]
theorem vu_permanent.variants.even_lower_bound {n : ℕ} (hn : 0 < n) (heven : Even n) :
    ((2 : ℚ≥0) ^ (n ^ 2))⁻¹ ≤ permanentProbability n 0 := by
  obtain ⟨k, rfl⟩ := heven
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let v := Fin.append (fun _ : Fin (k + 1) ↦ true) (fun _ : Fin (k + 1) ↦ false)
  have hsum : (∑ i, if v i then (1 : ℤ) else -1) = 0 := by
    rw [Fin.sum_univ_add]
    simp only [v, Fin.append_left, Fin.append_right]
    simp
  have hzero := (signPermanent_first_column (n := k + 1 + k) v).trans (mul_eq_zero_of_right _ hsum)
  rw [← hzero]
  exact single_matrix_lower_bound _

/-- Vu's bound for every rate is equivalent to the $n$th roots of the probabilities tending
to zero. This equivalence also applies at orders where the probability is exactly zero. -/
@[category API, AMS 15 60]
theorem vu_permanent.variants.root_iff :
    (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (permanentProbability n 0 : ℝ) ≤ Real.exp (-c * n)) ↔
    Tendsto (fun n : ℕ ↦ (permanentProbability n 0 : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 0) := by
  have step {n : ℕ} (hn : 0 < n) (c : ℝ) :
      (permanentProbability n 0 : ℝ) ^ (n : ℝ)⁻¹ ≤ Real.exp (-c) ↔
      (permanentProbability n 0 : ℝ) ≤ Real.exp (-c * n) := by
    rw [Real.rpow_inv_le_iff_of_pos (by positivity) (Real.exp_pos _).le (by exact_mod_cast hn),
      ← Real.exp_mul]
  constructor
  · intro h
    refine tendsto_order.2 ⟨fun a ha ↦ .of_forall fun n ↦ ha.trans_le (by positivity), ?_⟩
    intro b hb
    obtain ⟨c, hc, hcb⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const hb)).exists
    filter_upwards [eventually_gt_atTop (0 : ℕ), h c hc] with n hn hbound
    exact ((step hn c).mpr hbound).trans_lt hcb
  · intro h c hc
    filter_upwards [eventually_gt_atTop (0 : ℕ), h.eventually_lt_const (Real.exp_pos (-c))]
      with n hn hbound
    exact (step hn c).mp hbound.le

end Arxiv.«2005.02797»
