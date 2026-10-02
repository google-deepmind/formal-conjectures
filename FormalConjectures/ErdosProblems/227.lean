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

public import Mathlib

/-!
# Erdős Problem 227

Let `f = ∑ aₙ zⁿ` be an entire function which is not a polynomial. Is it true that if
`lim_{r → ∞} (maxₙ |aₙ rⁿ|) / (max_{|z| = r} |f z|)` exists then it must be `0`?

The answer is **no** (Clunie–Hayman, 1964): the limit can take any value in `[0, 1/2]`.
That construction is *not* formalized here; see the final remarks.
-/

@[expose] public section

open Filter Topology Metric Polynomial

namespace Erdos227

/-- The `n`-th Taylor coefficient of `f` at the origin, `aₙ = f⁽ⁿ⁾(0) / n!`. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

/-- The maximum term `μ(r) = maxₙ |aₙ| rⁿ` of the Taylor series of `f` at the origin. -/
noncomputable def maxTerm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖coeff f n‖ * r ^ n

/-- The maximum modulus `M(r) = max_{|z| = r} |f z|`. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere (0 : ℂ) r)

/-- The statement of Erdős Problem 227: for every entire non-polynomial `f`, if
`μ(r) / M(r)` converges as `r → ∞`, then its limit is `0`.
This statement is **false** (Clunie–Hayman); we only record it here. -/
def Statement : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (¬ ∃ p : ℂ[X], ∀ z, f z = p.eval z) →
    ∀ L : ℝ, Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L) → L = 0

/-- The maximum modulus is attained/bounded: the image of a sphere under `‖f‖` is bounded. -/
lemma bddAbove_image_sphere {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    BddAbove ((fun z => ‖f z‖) '' sphere (0 : ℂ) r) :=
  (isCompact_sphere 0 r).bddAbove_image (by fun_prop)

lemma norm_le_maxModulus {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) r) : ‖f z‖ ≤ maxModulus f r :=
  le_csSup (bddAbove_image_sphere hf r) ⟨z, hz, rfl⟩

/-- **Cauchy's estimate**: each term `|aₙ| rⁿ` is at most `M(r)`. -/
lemma norm_coeff_mul_pow_le_maxModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ}
    (hr : 0 < r) (n : ℕ) : ‖coeff f n‖ * r ^ n ≤ maxModulus f r := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    hf.diffContOnCl (fun z hz => norm_le_maxModulus hf.continuous hz)
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr n
  rw [coeff, norm_div, Complex.norm_natCast]
  rw [le_div_iff₀ hrn] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hfac]
  linarith

/-- The maximum term never exceeds the maximum modulus: `μ(r) ≤ M(r)`. -/
lemma maxTerm_le_maxModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    maxTerm f r ≤ maxModulus f r :=
  ciSup_le fun n => norm_coeff_mul_pow_le_maxModulus hf hr n

lemma maxTerm_nonneg (f : ℂ → ℂ) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ maxTerm f r :=
  Real.iSup_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n)

lemma maxModulus_nonneg {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ maxModulus f r :=
  (norm_nonneg _).trans (norm_le_maxModulus hf (z := (r : ℂ)) (by simp [abs_of_nonneg hr]))

/-- For every entire function, any limit of `μ(r) / M(r)` as `r → ∞` lies in `[0, 1]`. -/
theorem limit_mem_Icc {f : ℂ → ℂ} (hf : Differentiable ℂ f) {L : ℝ}
    (h : Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L)) : L ∈ Set.Icc 0 1 := by
  refine ⟨ge_of_tendsto h ?_, le_of_tendsto h ?_⟩ <;>
    filter_upwards [eventually_gt_atTop 0] with r hr
  · exact div_nonneg (maxTerm_nonneg f r hr.le) (maxModulus_nonneg hf.continuous hr.le)
  · exact div_le_one_of_le₀ (maxTerm_le_maxModulus hf hr) (maxModulus_nonneg hf.continuous hr.le)

lemma iteratedDeriv_polynomial_eval (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) = fun z => (derivative^[n] p).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext z
    exact Polynomial.deriv _

/-- The Taylor coefficients of a polynomial function are the polynomial's coefficients. -/
lemma coeff_polynomial_eval (p : ℂ[X]) (n : ℕ) : coeff (fun z => p.eval z) n = p.coeff n := by
  rw [coeff, iteratedDeriv_polynomial_eval]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

lemma maxModulus_polynomial_le (p : ℂ[X]) {r : ℝ} (hr : 0 ≤ r) :
    maxModulus (fun z => p.eval z) r ≤
      ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * r ^ k := by
  apply csSup_le
  · obtain ⟨z, hz⟩ : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.mpr hr
    exact ⟨_, z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ = r := by simpa using hz
    dsimp only
    rw [eval_eq_sum_range]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [hz']

/-- For a nonzero polynomial the ratio `μ(r) / M(r)` tends to `1`. In particular the
hypothesis "`f` is not a polynomial" in Erdős Problem 227 cannot be dropped. -/
theorem tendsto_maxTerm_div_maxModulus_polynomial (p : ℂ[X]) (hp : p ≠ 0) :
    Tendsto (fun r => maxTerm (fun z => p.eval z) r / maxModulus (fun z => p.eval z) r)
      atTop (𝓝 1) := by
  set f : ℂ → ℂ := fun z => p.eval z
  have hf : Differentiable ℂ f := p.differentiable
  set d := p.natDegree
  set c := ‖p.leadingCoeff‖
  have hc : 0 < c := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)
  -- the lower bound `c rᵈ / ∑ₖ |aₖ| rᵏ` tends to `1`
  have hlow : Tendsto (fun r : ℝ => c * r ^ d /
      ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ * r ^ k) atTop (𝓝 1) := by
    have hsum : ∀ r : ℝ, 0 < r → ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ * r ^ k =
        c * r ^ d * (1 + ∑ k ∈ Finset.range d, ‖p.coeff k‖ / c * (r⁻¹) ^ (d - k)) := by
      intro r hr
      rw [Finset.sum_range_succ, mul_add, mul_one, Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk : k ≤ d := (Finset.mem_range.mp hk).le
      rw [inv_pow, ← pow_sub_mul_pow r hk]
      field_simp
    have hT : Tendsto (fun r : ℝ =>
        (1 + ∑ k ∈ Finset.range d, ‖p.coeff k‖ / c * (r⁻¹) ^ (d - k))⁻¹) atTop (𝓝 1) := by
      have : Tendsto (fun r : ℝ =>
          1 + ∑ k ∈ Finset.range d, ‖p.coeff k‖ / c * (r⁻¹) ^ (d - k)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun r : ℝ =>
            ∑ k ∈ Finset.range d, ‖p.coeff k‖ / c * (r⁻¹) ^ (d - k)) atTop (𝓝 0) := by
          rw [show (0 : ℝ) = ∑ k ∈ Finset.range d, ‖p.coeff k‖ / c * 0 by simp]
          refine tendsto_finset_sum _ fun k hk => ?_
          refine Tendsto.const_mul _ ?_
          have hk : 0 < d - k := Nat.sub_pos_of_lt (Finset.mem_range.mp hk)
          have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow (d - k)
          rwa [zero_pow hk.ne'] at this
        simpa using h0.const_add 1
      simpa using this.inv₀ one_ne_zero
    refine hT.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [hsum r hr]
    have : 0 < c * r ^ d := mul_pos hc (pow_pos hr d)
    rw [div_mul_eq_div_div, div_self this.ne', one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have hμ : c * r ^ d ≤ maxTerm f r := by
      refine le_trans ?_ (le_ciSup ⟨maxModulus f r, ?_⟩ d)
      · simp only [f, coeff_polynomial_eval, c, d, Polynomial.leadingCoeff, le_refl]
      · rintro _ ⟨n, rfl⟩
        exact norm_coeff_mul_pow_le_maxModulus hf hr n
    have hM := maxModulus_polynomial_le p hr.le
    have hpos : 0 < c * r ^ d := mul_pos hc (pow_pos hr d)
    calc c * r ^ d / ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ * r ^ k
        ≤ c * r ^ d / maxModulus f r :=
          div_le_div_of_nonneg_left hpos.le
            (hpos.trans_le (hμ.trans (maxTerm_le_maxModulus hf hr))) hM
      _ ≤ maxTerm f r / maxModulus f r :=
          div_le_div_of_nonneg_right hμ (hpos.le.trans (hμ.trans (maxTerm_le_maxModulus hf hr)))
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact div_le_one_of_le₀ (maxTerm_le_maxModulus hf hr) (maxModulus_nonneg hf.continuous hr.le)

/-- Without the hypothesis "`f` is not a polynomial" the statement of Erdős Problem 227 is
false: the constant function `1` gives the limit `1`. -/
theorem not_statement_without_nonpolynomial_hypothesis :
    ¬ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      ∀ L : ℝ, Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L) → L = 0 := by
  intro h
  have := h (fun z => (1 : ℂ[X]).eval z) (1 : ℂ[X]).differentiable 1
    (tendsto_maxTerm_div_maxModulus_polynomial 1 one_ne_zero)
  exact one_ne_zero this

end Erdos227

/-!
## Remarks

* `Erdos227.Statement` is the faithful formal statement of the question. It is known to be
  false (Clunie–Hayman 1964 show that the limit can take any value in `[0, 1/2]`), but this
  file does **not** formalize that construction, so neither `Statement` nor `¬ Statement`
  is proved here.
* Proved here: Cauchy's estimate `μ(r) ≤ M(r)`, that any limit lies in `[0, 1]`, that for
  a nonzero polynomial the ratio tends to `1`, and hence that the non-polynomial hypothesis
  is necessary.
-/

