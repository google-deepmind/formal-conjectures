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
import FormalConjectures.Util.ProblemImports

/-!
# Positivity of the Veneziano amplitude in ten dimensions

*Reference:* [arxiv/2502.20372](https://arxiv.org/abs/2502.20372)
**Positivity of the Veneziano Amplitude in Ten Dimensions** by *Gareth Mansfield*

The (type-I, `α₀ = 0`) Veneziano amplitude is the Euler beta function
$$A(s,t) = \frac{\Gamma(-s)\,\Gamma(-t)}{\Gamma(1-s-t)}.$$
It is meromorphic with simple poles at non-negative integers `s = n`, and its residue there is
the polynomial in `t`
$$\operatorname{Res}_{s=n} A(s,t) = \frac{(t+1)_{(n-1)}}{n!}
  = \frac{(t+1)(t+2)\cdots(t+n-1)}{n!},$$
where `(a)_{(m)}` is the rising factorial.

Unitarity in `D` spacetime dimensions requires that, when this residue is written in the angular
variable `x = 1 + 2t/n` and expanded in the basis of Gegenbauer polynomials `C_j^{(λ)}` with
`λ = (D-3)/2` (the partial-wave / spin-`j` basis for the little group `O(D-1)`),
$$\operatorname{Res}_{s=n} A = \sum_j B_{n,j}^{D}\, C_j^{(λ)}(x),$$
all the partial-wave coefficients `B_{n,j}^D` are non-negative.

Mansfield proves this **positivity** holds for all `n, j` precisely when `D ≤ 10`, giving the first
direct, amplitude-level proof above `D ≤ 6`. Sharpness is visible already at level `n = 3`, spin
`0`, where (eq. 1.3)
$$B_{3,0}^{D} = \frac{10 - D}{24\,(D-1)},$$
which is negative as soon as `D > 10`.
-/

namespace Arxiv.«2502.20372»

open Polynomial

/--
The residue `Res_{s=n} A(s,t)` of the type-I Veneziano amplitude at the pole `s = n`, written as
a polynomial in the angular variable `x` via `t = n (x - 1) / 2`. Explicitly it is
`((t+1)(t+2)⋯(t+n-1)) / n!` with `t = n (x - 1) / 2`, a polynomial of degree `n - 1`.
-/
noncomputable def residueX (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ)⁻¹) *
    ∏ i ∈ Finset.range (n - 1), (C ((n : ℚ) / 2) * (X - 1) + C ((i : ℚ) + 1))

/-- The Gegenbauer parameter `λ = (D - 3) / 2` attached to spacetime dimension `D`. -/
noncomputable def lam (D : ℕ) : ℚ := ((D : ℚ) - 3) / 2

@[category test, AMS 81]
theorem residueX_one : residueX 1 = 1 := by
  simp [residueX]

/-- The level-3 residue in the angular variable: `Res_{s=3} = (9x² - 1)/24`. Validates `residueX`. -/
@[category test, AMS 81]
theorem residueX_three : residueX 3 = C (9 / 24 : ℚ) * X ^ 2 - C (1 / 24) := by
  apply Polynomial.funext
  intro x
  simp only [residueX, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Nat.factorial, eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_pow, eval_one]
  push_cast
  ring

/--
**Main theorem (Mansfield, 2025).** Partial-wave positivity of the type-I Veneziano amplitude in
`D ≤ 10`: at every massive level `n ≥ 1` the residue expands in the Gegenbauer (spin) basis
`C_j^{(λ)}`, `λ = (D-3)/2`, with non-negative coefficients. Equivalently, there is a non-negative
sequence of partial-wave coefficients realising the expansion.
-/
@[category research solved, AMS 33 81]
theorem partial_wave_positivity {D : ℕ} (hD : 3 ≤ D) (hD10 : D ≤ 10) {n : ℕ} (hn : 1 ≤ n) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      residueX n = ∑ j ∈ Finset.range n, C (B j) * gegenbauer (lam D) j := by
  sorry

/-- The Gegenbauer parameter `λ = (D-3)/2` is positive for `D ≥ 4`. -/
@[category API, AMS 33]
theorem lam_pos {D : ℕ} (hD : 4 ≤ D) : 0 < lam D := by
  have : (4 : ℚ) ≤ (D : ℚ) := by exact_mod_cast hD
  rw [lam]; linarith

/-- `partial_wave_positivity` at level `n = 1`: the residue is the positive scalar `B₁,₀ = 1`
(holds in every dimension). -/
@[category test, AMS 33 81]
theorem partial_wave_positivity_one (D : ℕ) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      residueX 1 = ∑ j ∈ Finset.range 1, C (B j) * gegenbauer (lam D) j := by
  refine ⟨fun j => if j = 0 then 1 else 0, fun j => by dsimp only; split <;> norm_num, ?_⟩
  rw [residueX_one, Finset.sum_range_one, gegenbauer_zero]
  norm_num

/-- `partial_wave_positivity` at level `n = 2`: only spin 1 contributes, coefficient `1/(4λ) > 0`
(holds for `D ≥ 4`). -/
@[category test, AMS 33 81]
theorem partial_wave_positivity_two {D : ℕ} (hD : 4 ≤ D) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      residueX 2 = ∑ j ∈ Finset.range 2, C (B j) * gegenbauer (lam D) j := by
  have hl := lam_pos hD
  refine ⟨fun j => if j = 1 then 1 / (4 * lam D) else 0, fun j => by
    dsimp only; split
    · positivity
    · norm_num, ?_⟩
  apply Polynomial.funext
  intro x
  rw [eval_finset_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, gegenbauer_zero,
    gegenbauer_one, residueX, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Nat.factorial, eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one, reduceIte]
  field_simp
  rw [if_neg (by decide : ¬ (0 : ℕ) = 1)]
  ring

/-- `partial_wave_positivity` at the critical level `n = 3`: spins 0 and 2 contribute, with
`B₃,₀ = (10-D)/(24(D-1)) ≥ 0` (needs `D ≤ 10`) and `B₃,₂ = 3/(4(D-3)(D-1)) > 0` (needs `D ≥ 4`).
This is exactly where the dimension bound becomes sharp. -/
@[category test, AMS 33 81]
theorem partial_wave_positivity_three {D : ℕ} (hD : 4 ≤ D) (hD10 : D ≤ 10) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      residueX 3 = ∑ j ∈ Finset.range 3, C (B j) * gegenbauer (lam D) j := by
  have hDQ : (4 : ℚ) ≤ (D : ℚ) := by exact_mod_cast hD
  have hD10Q : (D : ℚ) ≤ 10 := by exact_mod_cast hD10
  have h3 : (0 : ℚ) < (D : ℚ) - 3 := by linarith
  have h1 : (0 : ℚ) < (D : ℚ) - 1 := by linarith
  refine ⟨fun j => if j = 0 then (10 - (D : ℚ)) / (24 * ((D : ℚ) - 1))
                   else if j = 2 then 3 / (4 * ((D : ℚ) - 3) * ((D : ℚ) - 1)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split
    · exact div_nonneg (by linarith) (by linarith)
    · split
      · exact div_nonneg (by norm_num) (by positivity)
      · norm_num
  · apply Polynomial.funext
    intro x
    rw [eval_finset_sum, residueX_three]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, gegenbauer_zero,
      gegenbauer_one, gegenbauer_two, eval_mul, eval_sub, eval_C, eval_X, eval_one,
      eval_pow, reduceIte, lam]
    rw [if_neg (by decide : ¬ (1 : ℕ) = 0), if_neg (by decide : ¬ (1 : ℕ) = 2),
      if_neg (by decide : ¬ (2 : ℕ) = 0)]
    field_simp
    ring

/--
Gegenbauer linear independence (the engine behind uniqueness): for `0 < a`, the only way a
combination `∑_{j < n} B_j C_j^{(a)}` of the first `n` Gegenbauer polynomials can vanish is if
every coefficient is zero. Proved by reading off the top (degree `n-1`) coefficient and inducting.
-/
@[category API, AMS 33]
theorem gegenbauer_sum_eq_zero {a : ℚ} (ha : 0 < a) :
    ∀ (n : ℕ) (c : ℕ → ℚ),
      (∑ j ∈ Finset.range n, C (c j) * gegenbauer a j = 0) → ∀ j, j < n → c j = 0
  | 0 => fun _ _ j hj => absurd hj (Nat.not_lt_zero j)
  | (n + 1) => fun c h => by
    have hcoeff := congrArg (fun p : ℚ[X] => p.coeff n) h
    simp only [finset_sum_coeff, coeff_C_mul, coeff_zero] at hcoeff
    have hlow : ∀ j ∈ Finset.range n, c j * (gegenbauer a j).coeff n = 0 := fun j hj => by
      have hjn : (gegenbauer a j).natDegree < n :=
        lt_of_eq_of_lt (gegenbauer_natDegree_leadingCoeff ha j).1 (Finset.mem_range.mp hj)
      exact mul_eq_zero_of_right _ (coeff_eq_zero_of_natDegree_lt hjn)
    rw [Finset.sum_range_succ, Finset.sum_eq_zero hlow, zero_add] at hcoeff
    have hgn : (gegenbauer a n).coeff n = (gegenbauer a n).leadingCoeff := by
      unfold Polynomial.leadingCoeff; rw [(gegenbauer_natDegree_leadingCoeff ha n).1]
    rw [hgn] at hcoeff
    have hcn : c n = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_right (gegenbauer_natDegree_leadingCoeff ha n).2.ne'
    have hsum_n : ∑ j ∈ Finset.range n, C (c j) * gegenbauer a j = 0 := by
      rw [Finset.sum_range_succ, hcn, map_zero, zero_mul, add_zero] at h; exact h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | rfl
    · exact gegenbauer_sum_eq_zero ha n c hsum_n j hjn
    · exact hcn

/--
**Uniqueness of the partial-wave coefficients.** For `0 < a`, the Gegenbauer expansion of a
polynomial of degree `< n` is unique: this makes the partial-wave coefficients `B_{n,j}` (with
`a = (D-3)/2`, `D ≥ 4`) genuinely well-defined, not merely existent.
-/
@[category API, AMS 33]
theorem gegenbauer_expansion_unique {a : ℚ} (ha : 0 < a) (n : ℕ) (B B' : ℕ → ℚ)
    (h : ∑ j ∈ Finset.range n, C (B j) * gegenbauer a j
       = ∑ j ∈ Finset.range n, C (B' j) * gegenbauer a j) :
    ∀ j, j < n → B j = B' j := by
  intro j hj
  have hz : ∑ k ∈ Finset.range n, C (B k - B' k) * gegenbauer a k = 0 := by
    simp only [C_sub, sub_mul]
    rw [Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (gegenbauer_sum_eq_zero ha n (fun k => B k - B' k) hz j hj)

/--
The spin-`0` partial-wave coefficient at level `n = 3` is `B_{3,0}^D = (10 - D) / (24 (D-1))`
(eq. 1.3). Combined with uniqueness of the Gegenbauer expansion, this pins down the boundary
dimension: it is non-negative iff `D ≤ 10`.
-/
@[category research solved, AMS 81]
theorem B_three_zero {D : ℕ} (hD : 4 ≤ D) (B : ℕ → ℚ)
    (hB : residueX 3 = ∑ j ∈ Finset.range 3, C (B j) * gegenbauer (lam D) j) :
    B 0 = (10 - (D : ℚ)) / (24 * ((D : ℚ) - 1)) := by
  rw [residueX_three, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, gegenbauer_zero, gegenbauer_one, gegenbauer_two] at hB
  have e0 := congrArg (Polynomial.eval (0 : ℚ)) hB
  have e1 := congrArg (Polynomial.eval (1 : ℚ)) hB
  have em := congrArg (Polynomial.eval (-1 : ℚ)) hB
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one, eval_zero] at e0 e1 em
  -- Eliminating the spin-1 term: `(2λ+1)·e0 + (e1+e₋₁)/2` gives `(2λ+2)·B 0 = (7-2λ)/24`.
  have key : (2 * lam D + 2) * B 0 = (7 - 2 * lam D) / 24 := by
    linear_combination -(2 * lam D + 1) * e0 - e1 / 2 - em / 2
  have hDQ : (4 : ℚ) ≤ (D : ℚ) := by exact_mod_cast hD
  have hD1 : (D : ℚ) - 1 ≠ 0 := by intro h; nlinarith
  have key2 : ((D : ℚ) - 1) * B 0 = (10 - (D : ℚ)) / 24 := by
    rw [lam] at key; linear_combination key
  rw [eq_div_iff (mul_ne_zero (by norm_num) hD1)]
  linear_combination 24 * key2

/--
**Sharpness.** In `D = 11` the spin-`0` coefficient at level `3` is already negative
(`= -1/240`), so partial-wave positivity fails — consistency forces `D ≤ 10`.
-/
@[category test, AMS 81]
theorem partial_wave_negative_of_dim_eleven (B : ℕ → ℚ)
    (hB : residueX 3 = ∑ j ∈ Finset.range 3, C (B j) * gegenbauer (lam 11) j) :
    B 0 < 0 := by
  rw [B_three_zero (D := 11) (by norm_num) B hB]
  norm_num

/- ## Section 2 — the partial-wave projection by integration

Section 2 *defines* the partial-wave coefficients analytically (eq. 2.5): integrate the residue
polynomial against the Gegenbauer polynomials with respect to the weight `(1 - x²)^{(D-4)/2}` on
`[-1, 1]`, using Gegenbauer orthogonality to isolate each spin `j`. It then recasts this as the
double-contour integral (eq. 2.11) on which the positivity proof operates.

We formalise the integral side faithfully; the analytic identities are stated as benchmark
`sorry`s. (The contour form (2.11) is omitted pending complex-contour integration API.) -/

section Section2

open MeasureTheory

/-- The Gegenbauer weight `w_D(x) = (1 - x²)^{(D-4)/2}` on `[-1, 1]`. -/
noncomputable def weight (D : ℕ) (x : ℝ) : ℝ := (1 - x ^ 2) ^ (((D : ℝ) - 4) / 2)

/-- The real Gegenbauer parameter `λ = (D - 3) / 2`. -/
noncomputable def lamR (D : ℕ) : ℝ := ((D : ℝ) - 3) / 2

/--
The partial-wave coefficient `B_{n,j}^D` defined analytically as in eq. (2.5): the integral over
`[-1, 1]` of the level-`n` residue against the spin-`j` Gegenbauer polynomial, against the weight
`(1 - x²)^{(D-4)/2}`.
-/
noncomputable def Bintegral (D n j : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, weight D x * (gegenbauer (lamR D) j).eval x * aeval x (residueX n)

/-- The squared Gegenbauer norm `‖C_j^{(λ)}‖²` appearing in the projection (eq. 2.5). -/
noncomputable def gegenbauerNormSq (D j : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, weight D x * (gegenbauer (lamR D) j).eval x ^ 2

/-- **Gegenbauer orthogonality.** Distinct spins are orthogonal for the weight `(1 - x²)^{(D-4)/2}`. -/
@[category research solved, AMS 33]
theorem gegenbauer_orthogonal {D : ℕ} (hD : 3 ≤ D) {i j : ℕ} (hij : i ≠ j) :
    ∫ x in (-1 : ℝ)..1,
        weight D x * (gegenbauer (lamR D) i).eval x * (gegenbauer (lamR D) j).eval x = 0 := by
  sorry

/--
The Gegenbauer norm is strictly positive for `D ≥ 4`: the weight is positive on the open
interval and the polynomial is non-zero, so the squared integrand has positive support.
(`D = 3` must be excluded: there `λ = 0` and `C_1^{(0)} = 0`, so the norm vanishes.)
-/
@[category API, AMS 33]
theorem gegenbauerNormSq_pos {D : ℕ} (hD : 4 ≤ D) (j : ℕ) : 0 < gegenbauerNormSq D j := by
  have hDR : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have he : 0 ≤ ((D : ℝ) - 4) / 2 := by linarith
  have hl : 0 < lamR D := by rw [lamR]; linarith
  set g : Polynomial ℝ := gegenbauer (lamR D) j with hg
  have hgne : g ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp (gegenbauer_natDegree_leadingCoeff hl j).2.ne'
  set f : ℝ → ℝ := fun x => weight D x * g.eval x ^ 2 with hf
  have hwcont : Continuous (weight D) := by
    have h1 : Continuous fun x : ℝ => 1 - x ^ 2 := by continuity
    exact h1.rpow_const fun x => Or.inr he
  have hfc : Continuous f := hwcont.mul (g.continuous.pow 2)
  have hfi : IntervalIntegrable f MeasureTheory.volume (-1 : ℝ) 1 :=
    hfc.intervalIntegrable _ _
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc (-1 : ℝ) 1)] f := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hw : (0 : ℝ) ≤ weight D x :=
      Real.rpow_nonneg (by nlinarith [hx.1, hx.2] : (0 : ℝ) ≤ 1 - x ^ 2) _
    exact mul_nonneg hw (sq_nonneg _)
  have hroots : {x : ℝ | g.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hgne
  have hsubset : Set.Ioo (-1 : ℝ) 1 \ {x | g.IsRoot x}
      ⊆ Function.support f ∩ Set.Ioc (-1 : ℝ) 1 := by
    rintro x ⟨hx, hroot⟩
    have h1x : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hw : 0 < weight D x := Real.rpow_pos_of_pos h1x _
    have hgx : g.eval x ≠ 0 := fun h => hroot h
    have hfx : 0 < f x :=
      mul_pos hw (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hgx)))
    exact ⟨hfx.ne', hx.1, hx.2.le⟩
  have hmeas : 0 < MeasureTheory.volume (Function.support f ∩ Set.Ioc (-1 : ℝ) 1) := by
    refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsubset)
    rw [MeasureTheory.measure_diff_null (hroots.measure_zero MeasureTheory.volume),
      Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  show 0 < ∫ x in (-1 : ℝ)..1, f x
  exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg hfi).mpr
    ⟨by norm_num, hmeas⟩

/--
**Projection (eq. 2.5).** When the residue is written in the Gegenbauer basis with rational
coefficients `b`, the analytic coefficient `B_{n,j}^D` recovers `b_j` times the squared norm.
This is what makes `Bintegral` the partial-wave coefficient, and ties Section 2 to the algebraic
expansion used in `partial_wave_positivity`.
-/
@[category research solved, AMS 33 81]
theorem Bintegral_eq_coeff_mul_normSq {D n : ℕ} (hD : 3 ≤ D) (b : ℕ → ℚ)
    (hb : residueX n = ∑ k ∈ Finset.range n, C (b k) * gegenbauer (lam D) k) (j : ℕ) :
    Bintegral D n j = (b j : ℝ) * gegenbauerNormSq D j := by
  sorry

/--
**Positivity, integral form (Mansfield, 2025).** The analytically-defined partial-wave
coefficients are non-negative for `D ≤ 10` — the Section-2 statement of the main theorem.
-/
@[category research solved, AMS 33 81]
theorem Bintegral_nonneg {D : ℕ} (hD : 3 ≤ D) (hD10 : D ≤ 10) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    0 ≤ Bintegral D n j := by
  sorry

end Section2

end Arxiv.«2502.20372»
