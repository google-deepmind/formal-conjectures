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
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A nearly translation-invariant distribution on the lattice cube

This file constructs the discrete analogue of the density used by Karingula and Lovett in their
elementary proof of the Komlós conjecture. For a width $M$ we consider the *tent function*
$b(k) = \max\{M - |k|, 0\}$ on $\mathbb{Z}$ and the product $f(k) = \prod_j b(k_j)$ on
$\mathbb{Z}^d$. The *tent distribution* `Komlos.tentDist M d` is the probability distribution
proportional to $f^2$. It is supported in the cube $[-M, M]^d$, symmetric about the origin, and
`Komlos.two_thirds_le_overlap_tentDist` shows that for $M = 6N$ it has overlap at least $2/3$
with each of its translates by lattice vectors $w$ with $\|w\|_2 \le N$.

The proof follows the continuous argument of the paper with sums in place of integrals: the
$\ell^2$ distance between $f$ and its translate is controlled through the product structure, and
the overlap is bounded using the identity $\min\{a^2, b^2\} = (a^2 + b^2 - |a - b|(a + b))/2$
and the Cauchy–Schwarz inequality.

## References

* [S. R. Karingula and S. Lovett, *An elementary proof of the Komlós conjecture*,
  arXiv:2609.20979](https://arxiv.org/abs/2609.20979), Section 4.
-/

@[expose] public section

open Finset Function

namespace Komlos

/-! ### Auxiliary inequalities -/

/-- The Weierstrass product inequality `1 - ∑ aᵢ ≤ ∏ (1 - aᵢ)` for `aᵢ ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx, prod_insert hx]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) fun i hi => h1 i (mem_insert_of_mem hi)
    have hx0 := h0 x (mem_insert_self x s)
    have hx1 := h1 x (mem_insert_self x s)
    have hs0 : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hx1)]

theorem min_sq_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a ^ 2) (b ^ 2) = (a ^ 2 + b ^ 2 - |a - b| * (a + b)) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left (pow_le_pow_left₀ ha h 2), abs_of_nonpos (sub_nonpos.2 h)]
    ring
  · rw [min_eq_right (pow_le_pow_left₀ hb h 2), abs_of_nonneg (sub_nonneg.2 h)]
    ring

theorem support_shift_finite {G : Type*} [AddGroup G] {f : G → ℝ} (hf : (support f).Finite)
    (w : G) : (support fun k => f (k - w)).Finite := by
  have : (support fun k => f (k - w)) = (Equiv.subRight w) ⁻¹' support f := by
    ext k
    simp
  rw [this]
  exact hf.preimage (Equiv.injective _).injOn

theorem finsum_shift {G : Type*} [AddGroup G] (f : G → ℝ) (w : G) :
    ∑ᶠ k, f (k - w) = ∑ᶠ k, f k :=
  finsum_comp_equiv (Equiv.subRight w)

/-! ### The one-dimensional tent function -/

/-- The discrete tent function of width `M`: `tent M k = max (M - |k|) 0`. -/
noncomputable def tent (M : ℕ) (k : ℤ) : ℝ := max ((M : ℝ) - |(k : ℝ)|) 0

variable {M : ℕ}

theorem tent_nonneg (k : ℤ) : 0 ≤ tent M k := le_max_right _ _

theorem tent_neg (k : ℤ) : tent M (-k) = tent M k := by simp [tent]

theorem abs_lt_of_tent_ne_zero {k : ℤ} (hk : tent M k ≠ 0) : |k| < M := by
  by_contra! h
  apply hk
  have : (M : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast h
  simp [tent, sub_nonpos.2 this]

theorem tent_eq_zero_of_le {k : ℤ} (h : (M : ℤ) ≤ |k|) : tent M k = 0 := by
  by_contra hk
  exact absurd (abs_lt_of_tent_ne_zero hk) (not_lt.2 h)

theorem tent_of_abs_le {k : ℤ} (h : |k| ≤ M) : tent M k = M - |(k : ℝ)| := by
  have : |(k : ℝ)| ≤ M := by exact_mod_cast h
  rw [tent, max_eq_left (sub_nonneg.2 this)]

theorem support_tent_subset : support (tent M) ⊆ Finset.Icc (-(M : ℤ)) M := by
  intro k hk
  have := abs_lt.1 (abs_lt_of_tent_ne_zero hk)
  simp only [coe_Icc, Set.mem_Icc]
  omega

/-- The tent function is `1`-Lipschitz. -/
theorem abs_tent_sub_tent_le (k m : ℤ) : |tent M k - tent M (k - m)| ≤ |(m : ℝ)| :=
  calc |tent M k - tent M (k - m)|
      ≤ |((M : ℝ) - |(k : ℝ)|) - ((M : ℝ) - |((k - m : ℤ) : ℝ)|)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |(|(k : ℝ) - m| - |(k : ℝ)|)| := by
        congr 1
        push_cast
        ring
    _ ≤ |((k : ℝ) - m) - k| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |(m : ℝ)| := by rw [sub_sub_cancel_left, abs_neg]

theorem sum_range_sq (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem Icc_neg_eq_image (M : ℕ) :
    Finset.Icc (-(M : ℤ)) M = (range (2 * M + 1)).image fun i : ℕ => (i : ℤ) - M := by
  ext k
  simp only [mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(k + M).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

/-- The squared `ℓ²` norm of the tent function. -/
theorem finsum_tent_sq (M : ℕ) : ∑ᶠ k, tent M k ^ 2 = M * (2 * M ^ 2 + 1) / 3 := by
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(M : ℤ)) M)
      (fun k hk => support_tent_subset fun h => hk (by simp [h])),
    Icc_neg_eq_image, sum_image (fun a _ b _ h => by simpa using h)]
  rw [← sum_range_add_sum_Ico _ (show M + 1 ≤ 2 * M + 1 by omega), sum_Ico_eq_sum_range,
    show 2 * M + 1 - (M + 1) = M by omega]
  have h1 : ∀ i ∈ range (M + 1), tent M ((i : ℤ) - M) ^ 2 = (i : ℝ) ^ 2 := by
    intro i hi
    rw [mem_range] at hi
    rw [tent_of_abs_le (abs_le.2 ⟨by omega, by omega⟩)]
    push_cast
    rw [abs_of_nonpos (by linarith [(by exact_mod_cast Nat.lt_succ_iff.1 hi : (i : ℝ) ≤ M)])]
    ring
  have h2 : ∀ k ∈ range M, tent M (((M + 1 + k : ℕ) : ℤ) - M) ^ 2 = ((M - 1 - k : ℕ) : ℝ) ^ 2 := by
    intro k hk
    rw [mem_range] at hk
    rw [tent_of_abs_le (abs_le.2 ⟨by omega, by omega⟩)]
    have : ((M - 1 - k : ℕ) : ℝ) = M - 1 - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this]
    push_cast
    rw [abs_of_nonneg (by linarith [(by exact_mod_cast hk : (k : ℝ) < M)])]
    ring
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_range_reflect (fun k => (k : ℝ) ^ 2) M,
    sum_range_sq, sum_range_sq]
  push_cast
  ring

theorem finsum_tent_sq_pos (hM : 1 ≤ M) : 0 < ∑ᶠ k, tent M k ^ 2 := by
  rw [finsum_tent_sq]
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  positivity

theorem support_tent_shift_subset (m : ℤ) :
    support (fun k => tent M (k - m)) ⊆ Finset.Icc (-((M : ℤ) + |m|)) ((M : ℤ) + |m|) := by
  intro k hk
  have h1 := abs_lt_of_tent_ne_zero hk
  have h2 : |k| ≤ |k - m| + |m| := by simpa using abs_add_le (k - m) m
  simp only [coe_Icc, Set.mem_Icc]
  have := abs_le.1 (show |k| ≤ M + |m| by omega)
  omega

theorem support_tent_sub_sq_subset (m : ℤ) :
    support (fun k => (tent M k - tent M (k - m)) ^ 2) ⊆
      Finset.Icc (-((M : ℤ) + |m|)) ((M : ℤ) + |m|) := by
  intro k hk
  rw [mem_support] at hk
  simp only [coe_Icc, Set.mem_Icc]
  by_contra! h
  have hk' : (M : ℤ) + |m| < |k| := by
    rcases le_or_gt (-((M : ℤ) + |m|)) k with h' | h'
    · exact lt_abs.2 (Or.inl (h h'))
    · exact lt_abs.2 (Or.inr (by omega))
  have h1 : tent M k = 0 := tent_eq_zero_of_le (by linarith [abs_nonneg m])
  have h2 : tent M (k - m) = 0 :=
    tent_eq_zero_of_le (by linarith [abs_sub_abs_le_abs_sub k m])
  exact hk (by simp [h1, h2])

/-- Bound on the `ℓ²` distance between the tent function and its translate. -/
theorem finsum_tent_sub_sq_le (M : ℕ) (m : ℤ) :
    ∑ᶠ k, (tent M k - tent M (k - m)) ^ 2 ≤ (2 * M + 2 * |(m : ℝ)| + 1) * (m : ℝ) ^ 2 := by
  rw [finsum_eq_sum_of_support_subset _ (support_tent_sub_sq_subset m)]
  calc ∑ k ∈ Finset.Icc (-((M : ℤ) + |m|)) ((M : ℤ) + |m|), (tent M k - tent M (k - m)) ^ 2
      ≤ (Finset.Icc (-((M : ℤ) + |m|)) ((M : ℤ) + |m|)).card • (m : ℝ) ^ 2 := by
        refine sum_le_card_nsmul _ _ _ fun k _ => ?_
        rw [← sq_abs, ← sq_abs (m : ℝ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_tent_sub_tent_le k m) 2
    _ = (2 * M + 2 * |(m : ℝ)| + 1) * (m : ℝ) ^ 2 := by
        rw [Int.card_Icc, nsmul_eq_mul]
        congr 1
        have h : (((M : ℤ) + |m| + 1 - -((M : ℤ) + |m|)).toNat : ℝ) =
            (((M : ℤ) + |m| + 1 - -((M : ℤ) + |m|) : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [abs_nonneg m])]
        rw [h]
        push_cast
        ring

/-- Lower bound on the inner product of the tent function with its translate. -/
theorem finsum_tent_mul_shift_ge (M : ℕ) (m : ℤ) :
    ∑ᶠ k, tent M k ^ 2 - (2 * M + 2 * |(m : ℝ)| + 1) * (m : ℝ) ^ 2 / 2 ≤
      ∑ᶠ k, tent M k * tent M (k - m) := by
  set s := Finset.Icc (-((M : ℤ) + |m|)) ((M : ℤ) + |m|) with hs
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆ s := Icc_subset_Icc (by linarith [abs_nonneg m])
    (by linarith [abs_nonneg m])
  have hs1 : support (fun k => tent M k ^ 2) ⊆ ↑s := fun k hk =>
    hsub (support_tent_subset fun h => hk (by simp [h]))
  have hs2 : support (fun k => tent M (k - m) ^ 2) ⊆ ↑s := fun k hk =>
    support_tent_shift_subset m fun h => hk (by simp [h])
  have hs3 : support (fun k => tent M k * tent M (k - m)) ⊆ ↑s := fun k hk =>
    hsub (support_tent_subset (left_ne_zero_of_mul hk))
  have hshift : ∑ᶠ k, tent M (k - m) ^ 2 = ∑ᶠ k, tent M k ^ 2 :=
    finsum_shift (fun k => tent M k ^ 2) m
  have hexp : ∑ᶠ k, (tent M k - tent M (k - m)) ^ 2 =
      ∑ᶠ k, tent M k ^ 2 + ∑ᶠ k, tent M (k - m) ^ 2 - 2 * ∑ᶠ k, tent M k * tent M (k - m) := by
    rw [finsum_eq_sum_of_support_subset _ (support_tent_sub_sq_subset m),
      finsum_eq_sum_of_support_subset _ hs1, finsum_eq_sum_of_support_subset _ hs2,
      finsum_eq_sum_of_support_subset _ hs3, ← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have := finsum_tent_sub_sq_le M m
  linarith

/-! ### The product tent function on `ℤ^d` -/

/-- The product of tent functions on `ℤ^d`. -/
noncomputable def tentProd (M d : ℕ) (k : Fin d → ℤ) : ℝ := ∏ j, tent M (k j)

variable {d : ℕ}

theorem tentProd_nonneg (k : Fin d → ℤ) : 0 ≤ tentProd M d k :=
  prod_nonneg fun j _ => tent_nonneg (k j)

theorem tentProd_neg (k : Fin d → ℤ) : tentProd M d (-k) = tentProd M d k := by
  simp [tentProd, tent_neg]

theorem abs_lt_of_tentProd_ne_zero {k : Fin d → ℤ} (hk : tentProd M d k ≠ 0) (j : Fin d) :
    |k j| < M :=
  abs_lt_of_tent_ne_zero (prod_ne_zero_iff.1 hk j (mem_univ j))

theorem support_tentProd_subset :
    support (tentProd M d) ⊆ Fintype.piFinset fun _ : Fin d => Finset.Icc (-(M : ℤ)) M := by
  intro k hk
  rw [Fintype.coe_piFinset, Set.mem_univ_pi]
  intro j
  have := abs_lt.1 (abs_lt_of_tentProd_ne_zero hk j)
  rw [coe_Icc, Set.mem_Icc]
  omega

theorem support_tentProd_finite : (support (tentProd M d)).Finite :=
  (Finset.finite_toSet _).subset support_tentProd_subset

theorem support_tentProd_sq_finite : (support fun k => tentProd M d k ^ 2).Finite :=
  support_tentProd_finite.subset fun _ hk => (pow_ne_zero_iff two_ne_zero).1 hk

/-- Fubini for products of finitely supported one-dimensional functions. -/
theorem finsum_prod_eq_prod_finsum (g : Fin d → ℤ → ℝ) (B : Finset ℤ)
    (hg : ∀ j, support (g j) ⊆ B) :
    ∑ᶠ k : Fin d → ℤ, ∏ j, g j (k j) = ∏ j, ∑ᶠ x, g j x := by
  rw [finsum_eq_sum_of_support_subset _ (s := Fintype.piFinset fun _ => B) fun k hk => ?_]
  · rw [← prod_univ_sum]
    exact prod_congr rfl fun j _ => (finsum_eq_sum_of_support_subset _ (hg j)).symm
  · rw [Fintype.coe_piFinset, Set.mem_univ_pi]
    exact fun j => hg j (prod_ne_zero_iff.1 hk j (mem_univ j))

theorem finsum_tentProd_mul_shift (M d : ℕ) (w : Fin d → ℤ) :
    ∑ᶠ k, tentProd M d k * tentProd M d (k - w) =
      ∏ j, ∑ᶠ x, tent M x * tent M (x - w j) := by
  have h : ∀ k, tentProd M d k * tentProd M d (k - w) =
      ∏ j, tent M (k j) * tent M (k j - w j) := fun k => by
    simp [tentProd, prod_mul_distrib]
  simp only [h]
  exact finsum_prod_eq_prod_finsum (fun j x => tent M x * tent M (x - w j))
    (Finset.Icc (-(M : ℤ)) M) fun j x hx => support_tent_subset (left_ne_zero_of_mul hx)

theorem finsum_tentProd_sq (M d : ℕ) :
    ∑ᶠ k, tentProd M d k ^ 2 = (∑ᶠ x, tent M x ^ 2) ^ d := by
  have := finsum_tentProd_mul_shift M d 0
  simp only [Pi.zero_apply, sub_zero, ← sq, prod_const, card_univ, Fintype.card_fin] at this
  exact this

theorem finsum_tentProd_sq_pos (hM : 1 ≤ M) : 0 < ∑ᶠ k, tentProd M d k ^ 2 := by
  rw [finsum_tentProd_sq]
  exact pow_pos (finsum_tent_sq_pos hM) d

/-- The key estimate: for `M = 6 N` and `‖w‖₂ ≤ N`, the overlap of the unnormalised
distribution `tentProd M d ^ 2` with its translate by `w` is at least two thirds of its mass. -/
theorem two_thirds_mul_finsum_le_finsum_min (N d : ℕ) (hN : 1 ≤ N) (w : Fin d → ℤ)
    (hw : ∑ j, (w j : ℝ) ^ 2 ≤ N ^ 2) :
    2 / 3 * ∑ᶠ k, tentProd (6 * N) d k ^ 2 ≤
      ∑ᶠ k, min (tentProd (6 * N) d k ^ 2) (tentProd (6 * N) d (k - w) ^ 2) := by
  set M := 6 * N with hM
  set f := tentProd M d with hf
  set z := ∑ᶠ x, tent M x ^ 2 with hz
  set Z := ∑ᶠ k, f k ^ 2 with hZ
  have hzval : z = M * (2 * M ^ 2 + 1) / 3 := finsum_tent_sq M
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (M : ℝ) = 6 * N := by rw [hM]; push_cast; ring
  have hzpos : 0 < z := finsum_tent_sq_pos (by omega)
  have hZ' : Z = z ^ d := finsum_tentProd_sq M d
  have hZpos : 0 < Z := by rw [hZ']; positivity
  -- coordinate bounds
  have hwj : ∀ j, |(w j : ℝ)| ≤ N := fun j => by
    have h1 : (w j : ℝ) ^ 2 ≤ N ^ 2 :=
      (single_le_sum (fun i _ => sq_nonneg (w i : ℝ)) (mem_univ j)).trans hw
    rw [← sq_abs] at h1
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h1
  have hwj' : ∀ j, (w j : ℝ) ^ 2 ≤ N ^ 2 := fun j => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hwj j) 2
  -- one-dimensional inner products
  set c : Fin d → ℝ := fun j => (2 * M + 2 * |(w j : ℝ)| + 1) * (w j : ℝ) ^ 2 / 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hcz : ∀ j, c j ≤ z := fun j => by
    have h1 := hwj j
    have h2 := hwj' j
    have h3 : c j ≤ (2 * M + 2 * N + 1) * N ^ 2 / 2 := by
      simp only [hc]
      gcongr
    rw [hzval, hMN] at *
    nlinarith
  have hsumc : ∑ j, c j ≤ z / 18 := by
    calc ∑ j, c j ≤ ∑ j, (2 * M + 2 * N + 1) * (w j : ℝ) ^ 2 / 2 := sum_le_sum fun j _ => by
          simp only [hc]
          gcongr
          exact hwj j
      _ = (2 * M + 2 * N + 1) / 2 * ∑ j, (w j : ℝ) ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ ≤ (2 * M + 2 * N + 1) / 2 * N ^ 2 := by gcongr
      _ ≤ z / 18 := by
          rw [hzval, hMN]
          nlinarith
  have hip : ∀ j, z - c j ≤ ∑ᶠ x, tent M x * tent M (x - w j) := fun j =>
    finsum_tent_mul_shift_ge M (w j)
  -- inner product of `f` with its translate
  set ip := ∑ᶠ k, f k * f (k - w) with hip_def
  have hip_eq : ip = ∏ j, ∑ᶠ x, tent M x * tent M (x - w j) := finsum_tentProd_mul_shift M d w
  have hip_ge : 17 / 18 * Z ≤ ip := by
    rw [hip_eq, hZ']
    have hzd : z ^ d = ∏ _j : Fin d, z := by simp
    calc 17 / 18 * z ^ d ≤ (1 - ∑ j, c j / z) * z ^ d := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← sum_div]
          have : (∑ j, c j) / z ≤ 1 / 18 := by
            rw [div_le_iff₀ hzpos]
            linarith
          linarith
      _ ≤ (∏ j, (1 - c j / z)) * z ^ d := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact one_sub_sum_le_prod_one_sub _ _ (fun j _ => div_nonneg (hc0 j) hzpos.le)
            fun j _ => (div_le_one hzpos).2 (hcz j)
      _ = ∏ j, (z - c j) := by
          rw [hzd, ← prod_mul_distrib]
          exact prod_congr rfl fun j _ => by
            rw [sub_mul, div_mul_cancel₀ _ hzpos.ne', one_mul]
      _ ≤ ∏ j, ∑ᶠ x, tent M x * tent M (x - w j) :=
          prod_le_prod (fun j _ => by linarith [hcz j]) fun j _ => hip j
  -- pass to sums over a common finite set
  have hfin1 : (support fun k => f k ^ 2).Finite := support_tentProd_sq_finite
  have hfin2 : (support fun k => f (k - w) ^ 2).Finite := support_shift_finite hfin1 w
  set s := (hfin1.union hfin2).toFinset with hs
  have hmem : ∀ k, f k ≠ 0 ∨ f (k - w) ≠ 0 → k ∈ s := fun k h => by
    rw [hs, Set.Finite.mem_toFinset, Set.mem_union, mem_support, mem_support]
    rcases h with h | h
    · exact Or.inl (pow_ne_zero 2 h)
    · exact Or.inr (pow_ne_zero 2 h)
  have hshift : ∑ᶠ k, f (k - w) ^ 2 = Z := finsum_shift (fun k => f k ^ 2) w
  have e1 : Z = ∑ k ∈ s, f k ^ 2 :=
    finsum_eq_sum_of_support_subset _ fun k hk =>
      hmem k (Or.inl ((pow_ne_zero_iff two_ne_zero).1 hk))
  have e2 : ∑ᶠ k, f (k - w) ^ 2 = ∑ k ∈ s, f (k - w) ^ 2 :=
    finsum_eq_sum_of_support_subset _ fun k hk =>
      hmem k (Or.inr ((pow_ne_zero_iff two_ne_zero).1 hk))
  have e3 : ip = ∑ k ∈ s, f k * f (k - w) :=
    finsum_eq_sum_of_support_subset _ fun k hk => hmem k (Or.inl (left_ne_zero_of_mul hk))
  have e4 : ∑ᶠ k, min (f k ^ 2) (f (k - w) ^ 2) = ∑ k ∈ s, min (f k ^ 2) (f (k - w) ^ 2) :=
    finsum_eq_sum_of_support_subset _ fun k hk => hmem k (Or.inl fun h => hk (by
      show min (f k ^ 2) (f (k - w) ^ 2) = 0
      rw [h, zero_pow two_ne_zero, min_eq_left (sq_nonneg _)]))
  have hB : ∑ k ∈ s, f (k - w) ^ 2 = ∑ k ∈ s, f k ^ 2 := by rw [← e2, hshift, e1]
  have hminus : ∑ k ∈ s, (f k - f (k - w)) ^ 2 = 2 * Z - 2 * ip := by
    have : ∑ k ∈ s, (f k - f (k - w)) ^ 2 =
        ∑ k ∈ s, f k ^ 2 + ∑ k ∈ s, f (k - w) ^ 2 - 2 * ∑ k ∈ s, f k * f (k - w) := by
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [this, hB, ← e1, ← e3]
    ring
  have hplus : ∑ k ∈ s, (f k + f (k - w)) ^ 2 = 2 * Z + 2 * ip := by
    have : ∑ k ∈ s, (f k + f (k - w)) ^ 2 =
        ∑ k ∈ s, f k ^ 2 + ∑ k ∈ s, f (k - w) ^ 2 + 2 * ∑ k ∈ s, f k * f (k - w) := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [this, hB, ← e1, ← e3]
    ring
  have hip_le : ip ≤ Z := by
    have : 0 ≤ ∑ k ∈ s, (f k - f (k - w)) ^ 2 := sum_nonneg fun k _ => sq_nonneg _
    linarith
  set D := ∑ k ∈ s, |f k - f (k - w)| * (f k + f (k - w)) with hD
  have hD0 : 0 ≤ D := sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg (tentProd_nonneg _) (tentProd_nonneg _))
  have hCS : D ^ 2 ≤ (∑ k ∈ s, (f k - f (k - w)) ^ 2) * ∑ k ∈ s, (f k + f (k - w)) ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq s (fun k => |f k - f (k - w)|) fun k => f k + f (k - w)
    simpa only [sq_abs] using this
  have hDle : D ≤ 2 / 3 * Z := by
    refine (pow_le_pow_iff_left₀ hD0 (by positivity) two_ne_zero).1 (hCS.trans ?_)
    rw [hminus, hplus]
    nlinarith [mul_le_mul hip_ge hip_ge (by positivity) (by linarith)]
  have hmin : ∑ k ∈ s, min (f k ^ 2) (f (k - w) ^ 2) =
      (∑ k ∈ s, f k ^ 2 + ∑ k ∈ s, f (k - w) ^ 2 - D) / 2 := by
    rw [hD, ← sum_add_distrib, ← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun k _ => min_sq_eq _ _ (tentProd_nonneg _) (tentProd_nonneg _)
  rw [e4, hmin, hB, ← e1]
  linarith

/-! ### The tent distribution -/

theorem support_tentProd_sq_div_finite (M d : ℕ) (Z : ℝ) :
    (support fun k => tentProd M d k ^ 2 / Z).Finite :=
  support_tentProd_finite.subset fun k hk => by
    rw [mem_support] at hk ⊢
    exact fun h => hk (by
      show tentProd M d k ^ 2 / Z = 0
      rw [h]
      simp)

/-- The tent distribution: the probability distribution on `ℤ^d` proportional to
`tentProd M d ^ 2`. -/
noncomputable def tentDist (M d : ℕ) : (Fin d → ℤ) →₀ ℝ :=
  Finsupp.ofSupportFinite (fun k => tentProd M d k ^ 2 / ∑ᶠ x, tentProd M d x ^ 2)
    (support_tentProd_sq_div_finite M d _)

@[simp]
theorem tentDist_apply (k : Fin d → ℤ) :
    tentDist M d k = tentProd M d k ^ 2 / ∑ᶠ x, tentProd M d x ^ 2 := rfl

theorem tentDist_nonneg (k : Fin d → ℤ) : 0 ≤ tentDist M d k :=
  div_nonneg (sq_nonneg _) (finsum_nonneg fun _ => sq_nonneg _)

theorem tentDist_neg (k : Fin d → ℤ) : tentDist M d (-k) = tentDist M d k := by
  simp [tentProd_neg]

theorem abs_lt_of_tentDist_ne_zero {k : Fin d → ℤ} (hk : tentDist M d k ≠ 0) (j : Fin d) :
    |k j| < M :=
  abs_lt_of_tentProd_ne_zero (fun h => hk (by simp [h])) j

theorem isProbDist_tentDist (hM : 1 ≤ M) : (tentDist M d).IsProbDist where
  nonneg := tentDist_nonneg
  mass_eq_one := by
    have hZ : 0 < ∑ᶠ x, tentProd M d x ^ 2 := finsum_tentProd_sq_pos hM
    rw [Finsupp.mass, Finsupp.sum,
      ← finsum_eq_sum_of_support_subset _ (Finsupp.fun_support_eq _).le]
    simp only [tentDist_apply, div_eq_mul_inv]
    rw [← finsum_mul, mul_inv_cancel₀ hZ.ne']

theorem overlap_tentDist (M d : ℕ) (w : Fin d → ℤ) :
    (tentDist M d).overlap w =
      (∑ᶠ k, min (tentProd M d k ^ 2) (tentProd M d (k - w) ^ 2)) /
        ∑ᶠ x, tentProd M d x ^ 2 := by
  have hZ : 0 ≤ ∑ᶠ x, tentProd M d x ^ 2 := finsum_nonneg fun _ => sq_nonneg _
  rw [Finsupp.overlap, Finsupp.sum,
    ← finsum_eq_sum_of_support_subset _ (s := (tentDist M d).support) ?_]
  · simp only [tentDist_apply]
    rw [finsum_congr fun k => min_div_div_right hZ _ _]
    simp only [div_eq_mul_inv]
    rw [← finsum_mul]
  · intro k hk
    rw [mem_support] at hk
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun h => hk (by rw [h, min_eq_left (tentDist_nonneg _)])

/-- For `M = 6 N`, the tent distribution has overlap at least `2 / 3` with its translate by any
lattice vector of Euclidean norm at most `N`. -/
theorem two_thirds_le_overlap_tentDist (N d : ℕ) (hN : 1 ≤ N) (w : Fin d → ℤ)
    (hw : ∑ j, (w j : ℝ) ^ 2 ≤ N ^ 2) :
    2 / 3 ≤ (tentDist (6 * N) d).overlap w := by
  have hZ : 0 < ∑ᶠ x, tentProd (6 * N) d x ^ 2 := finsum_tentProd_sq_pos (by omega)
  rw [overlap_tentDist, le_div_iff₀ hZ]
  exact two_thirds_mul_finsum_le_finsum_min N d hN w hw

end Komlos
