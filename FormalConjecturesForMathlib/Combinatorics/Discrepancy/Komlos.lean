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

public import FormalConjecturesForMathlib.Combinatorics.Discrepancy.Balancing
public import FormalConjecturesForMathlib.Combinatorics.Discrepancy.TentDistribution
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr

/-!
# The Komlós conjecture

This file proves the Komlós conjecture with the constant $36$, following the elementary proof
of Karingula and Lovett: for all vectors $v_1, \dots, v_n \in \mathbb{R}^d$ with
$\|v_i\|_2 \le 1$ there are signs $\varepsilon_i \in \{-1, 1\}$ such that
$\|\sum_i \varepsilon_i v_i\|_\infty \le 36$.

The main result is `Komlos.exists_signs_abs_sum_le`. Its proof combines the balancing lemma
`Finsupp.exists_signs_isProbDist_mean_eq` with the tent distribution
`Komlos.tentDist`, transported to $\mathbb{R}^d$ along the map $k \mapsto k / N$. This proves
the statement for vectors with coordinates in $N^{-1}\mathbb{Z}$; the general case follows by
truncating the coordinates toward zero and using that there are only finitely many sign vectors.

## References

* [S. R. Karingula and S. Lovett, *An elementary proof of the Komlós conjecture*,
  arXiv:2609.20979](https://arxiv.org/abs/2609.20979)
-/

@[expose] public section

open Finset Function

namespace Komlos

variable {d : ℕ}

/-! ### The tent distribution on `ℝ^d` -/

/-- The embedding `ℤ^d → ℝ^d`, `k ↦ k / N`. -/
noncomputable def latticeHom (N d : ℕ) : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun k j := (k j : ℝ) / N
  map_zero' := by
    ext
    simp
  map_add' k l := by
    ext
    simp [add_div]

theorem latticeHom_apply (N : ℕ) (k : Fin d → ℤ) (j : Fin d) :
    latticeHom N d k j = (k j : ℝ) / N := rfl

theorem latticeHom_injective {N : ℕ} (hN : 1 ≤ N) : Injective (latticeHom N d) := by
  intro k l h
  ext j
  have hj := congrFun h j
  simp only [latticeHom_apply] at hj
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  exact_mod_cast (div_left_inj' hN').1 hj

/-- The tent distribution of width `6 N` transported to `ℝ^d` along `k ↦ k / N`. -/
noncomputable def realTentDist (N d : ℕ) : (Fin d → ℝ) →₀ ℝ :=
  Finsupp.mapDomain (latticeHom N d) (tentDist (6 * N) d)

theorem isProbDist_realTentDist {N : ℕ} (hN : 1 ≤ N) : (realTentDist N d).IsProbDist :=
  ⟨Finsupp.mapDomain_apply_nonneg _ tentDist_nonneg, by
    rw [realTentDist, Finsupp.mass_mapDomain, (isProbDist_tentDist (by omega)).mass_eq_one]⟩

theorem abs_le_of_realTentDist_ne_zero {N : ℕ} (hN : 1 ≤ N) {x : Fin d → ℝ}
    (hx : realTentDist N d x ≠ 0) (j : Fin d) : |x j| ≤ 6 := by
  classical
  obtain ⟨k, hk, rfl⟩ := mem_image.1 (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hx))
  have h := abs_lt_of_tentDist_ne_zero (Finsupp.mem_support_iff.1 hk) j
  have h' : ((|k j| : ℤ) : ℝ) ≤ ((6 * N : ℕ) : ℤ) := by exact_mod_cast h.le
  push_cast at h'
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [latticeHom_apply, abs_div, Nat.abs_cast, div_le_iff₀ hN']
  linarith

theorem mean_realTentDist (N d : ℕ) : (realTentDist N d).mean = 0 := by
  rw [realTentDist, Finsupp.mean, Finsupp.sum_mapDomain_index (h := fun x (p : ℝ) => p • x)
    (fun _ => zero_smul ℝ _) (fun _ _ _ => add_smul _ _ _)]
  set x := (tentDist (6 * N) d).sum fun k p => p • latticeHom N d k with hx
  have hneg : x = -x := by
    rw [hx]
    unfold Finsupp.sum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_equiv (Equiv.neg _) (fun k => ?_) fun k _ => ?_
    · simp only [Finsupp.mem_support_iff, Equiv.neg_apply, tentDist_neg]
    · simp only [Equiv.neg_apply, tentDist_neg, map_neg, smul_neg, neg_neg]
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem overlap_realTentDist {N : ℕ} (hN : 1 ≤ N) (w : Fin d → ℤ) :
    (realTentDist N d).overlap (latticeHom N d w) = (tentDist (6 * N) d).overlap w := by
  rw [realTentDist, Finsupp.overlap, Finsupp.overlap,
    Finsupp.sum_mapDomain_index_inj (latticeHom_injective hN)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [← map_sub, Finsupp.mapDomain_apply (latticeHom_injective hN)]

/-! ### The Komlós bound -/

/-- The Komlós bound for vectors with coordinates in `N⁻¹ ℤ`: if `w i ∈ ℤ^d` satisfy
`∑ j, (w i j)² ≤ N²`, then there are signs `ε i ∈ {-1, 1}` with
`|∑ i, ε i * (w i j / N)| ≤ 36` for every coordinate `j`. -/
theorem exists_signs_abs_sum_div_le {N : ℕ} (hN : 1 ≤ N) {n : ℕ} (w : Fin n → Fin d → ℤ)
    (hw : ∀ i, ∑ j, (w i j : ℝ) ^ 2 ≤ N ^ 2) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ j, |∑ i, ε i * ((w i j : ℝ) / N)| ≤ 36 := by
  obtain ⟨ε, hε, R, hR, hRP, hmean⟩ := Finsupp.exists_signs_isProbDist_mean_eq n
    (fun i => (6 : ℝ)⁻¹ • latticeHom N d (w i)) (realTentDist N d)
    (isProbDist_realTentDist hN) fun i => by
      rw [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℝ) ≠ 0), one_smul,
        overlap_realTentDist hN]
      exact two_thirds_le_overlap_tentDist N d hN (w i) (hw i)
  refine ⟨ε, hε, fun j => ?_⟩
  have hbox := Finsupp.abs_mean_apply_le hR
    (fun x hx => abs_le_of_realTentDist_ne_zero hN (hRP x hx)) j
  rw [hmean, mean_realTentDist, zero_add] at hbox
  simp only [Finset.sum_apply, Pi.smul_apply, latticeHom_apply, smul_eq_mul] at hbox
  have h6 : ∑ i, ε i * ((w i j : ℝ) / N) = 6 * ∑ i, ε i * (6⁻¹ * ((w i j : ℝ) / N)) := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [h6, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  linarith

/-- Truncation of a real number toward zero. -/
noncomputable def truncToward (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉

theorem abs_truncToward_le (x : ℝ) : |(truncToward x : ℝ)| ≤ |x| := by
  unfold truncToward
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.2 h), abs_of_nonneg h]
    exact Int.floor_le x
  · have h' := not_le.1 h
    rw [abs_of_nonpos (by exact_mod_cast Int.ceil_nonpos.2 h'.le), abs_of_neg h']
    linarith [Int.le_ceil x]

theorem abs_sub_truncToward_le (x : ℝ) : |x - truncToward x| ≤ 1 := by
  unfold truncToward
  split_ifs
  · rw [abs_of_nonneg (sub_nonneg.2 (Int.floor_le x))]
    linarith [Int.lt_floor_add_one x]
  · rw [abs_of_nonpos (sub_nonpos.2 (Int.le_ceil x))]
    linarith [Int.ceil_lt_add_one x]

/-- Approximation step: for every `N`, some choice of signs balances `v` up to
`36 + n / (N + 1)`. -/
theorem exists_signs_abs_sum_le_add {n : ℕ} (v : Fin n → Fin d → ℝ) (hv : ∀ i, ∑ j, v i j ^ 2 ≤ 1)
    (N : ℕ) :
    ∃ σ : Fin n → Bool, ∀ j,
      |∑ i, (if σ i then 1 else -1 : ℝ) * v i j| ≤ 36 + n / (N + 1) := by
  set w : Fin n → Fin d → ℤ := fun i j => truncToward ((N + 1 : ℕ) * v i j) with hw_def
  have hN' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hw : ∀ i, ∑ j, (w i j : ℝ) ^ 2 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := fun i => by
    calc ∑ j, (w i j : ℝ) ^ 2 ≤ ∑ j, (((N + 1 : ℕ) : ℝ) * v i j) ^ 2 :=
          sum_le_sum fun j _ => by
            rw [← sq_abs, ← sq_abs (((N + 1 : ℕ) : ℝ) * v i j)]
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncToward_le _) 2
      _ = ((N + 1 : ℕ) : ℝ) ^ 2 * ∑ j, v i j ^ 2 := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by nlinarith [hv i]
  obtain ⟨ε, hε, hbound⟩ := exists_signs_abs_sum_div_le (by omega) w hw
  refine ⟨fun i => decide (ε i = 1), fun j => ?_⟩
  have hεeq : ∀ i, (if decide (ε i = 1) then 1 else -1 : ℝ) = ε i := fun i => by
    rcases hε i with h | h
    · simp [h]
    · simp [h, show ¬ ((-1 : ℝ) = 1) by norm_num]
  have hε1 : ∀ i, |ε i| = 1 := fun i => by
    rcases hε i with h | h
    · rw [h, abs_one]
    · rw [h, abs_neg, abs_one]
  simp only [hεeq]
  calc |∑ i, ε i * v i j|
      = |∑ i, ε i * ((w i j : ℝ) / (N + 1 : ℕ)) +
          ∑ i, ε i * (v i j - (w i j : ℝ) / (N + 1 : ℕ))| := by
        rw [← sum_add_distrib]
        congr 1
        exact sum_congr rfl fun i _ => by ring
    _ ≤ |∑ i, ε i * ((w i j : ℝ) / (N + 1 : ℕ))| +
          |∑ i, ε i * (v i j - (w i j : ℝ) / (N + 1 : ℕ))| := abs_add_le _ _
    _ ≤ 36 + ∑ i, |ε i * (v i j - (w i j : ℝ) / (N + 1 : ℕ))| :=
        add_le_add (hbound j) (abs_sum_le_sum_abs _ _)
    _ ≤ 36 + ∑ _i : Fin n, (1 : ℝ) / (N + 1 : ℕ) := by
        gcongr with i
        rw [abs_mul, hε1 i, one_mul]
        have : v i j - (w i j : ℝ) / (N + 1 : ℕ) = ((N + 1 : ℕ) * v i j - w i j) / (N + 1 : ℕ) := by
          field_simp
        rw [this, abs_div, abs_of_pos hN']
        exact div_le_div_of_nonneg_right (abs_sub_truncToward_le _) hN'.le
    _ = 36 + n / (N + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **The Komlós conjecture** with constant `36` (Karingula–Lovett). For vectors
`v i ∈ ℝ^d` with `∑ j, v i j ^ 2 ≤ 1` there are signs `ε i ∈ {-1, 1}` such that
`|∑ i, ε i * v i j| ≤ 36` for every coordinate `j`. -/
theorem exists_signs_abs_sum_le {n : ℕ} (v : Fin n → Fin d → ℝ) (hv : ∀ i, ∑ j, v i j ^ 2 ≤ 1) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ j, |∑ i, ε i * v i j| ≤ 36 := by
  have happrox := exists_signs_abs_sum_le_add v hv
  choose σ hσ using happrox
  obtain ⟨σ₀, hσ₀⟩ := Finite.exists_infinite_fiber σ
  refine ⟨fun i => if σ₀ i then 1 else -1, fun i => by by_cases h : σ₀ i <;> simp [h], fun j => ?_⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt (n / δ)
  obtain ⟨N, hN, hKN⟩ := (Set.infinite_coe_iff.1 hσ₀).exists_gt K
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hN
  have hspec := hσ N j
  rw [hN] at hspec
  refine hspec.trans ?_
  have hKN' : (K : ℝ) < N := by exact_mod_cast hKN
  rw [div_lt_iff₀ hδ] at hK
  have : (n : ℝ) / (N + 1) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Komlos
