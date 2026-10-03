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

import FormalConjecturesUtil

/-!
# Crouzeix's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Crouzeix%27s_conjecture)
* [Cr04] Crouzeix, M. (2004). "Bounds for analytical functions of matrices."
  *Integral Equations Operator Theory* 48, pp. 461--477.
* [Cr07] Crouzeix, M. (2007). "Numerical range and functional calculus in Hilbert space."
  *J. Funct. Anal.* 244, pp. 668--690.
* [CP17] Crouzeix, M. and Palencia, C. (2017). "The numerical range is a $(1+\sqrt{2})$-spectral
  set." *SIAM J. Matrix Anal. Appl.* 38, pp. 649--655.
-/

open Polynomial ComplexInnerProductSpace

namespace CrouzeixConjecture

/-- The **numerical range** `W(T)` of an operator `T` on a finite-dimensional complex Hilbert
space: the set of values `⟪x, T x⟫` over unit vectors `x`. -/
def numericalRange {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ⟪x, T x⟫ = z}

/--
**Crouzeix's conjecture (2004).**

For every complex square matrix `T` (viewed as an operator on `ℂⁿ`) and every polynomial `p`,
$$\|p(T)\| \le 2 \sup_{z \in W(T)} |p(z)|,$$
where `W(T)` is the numerical range of `T` and the left-hand side is the operator norm.
Crouzeix [Cr07] proved the inequality with constant `11.08`; Crouzeix and Palencia [CP17]
improved this to `1 + √2`. The constant `2` would be optimal (see `variants.sharp`).
-/
@[category research open, AMS 15 47]
theorem crouzeix_conjecture {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ 2 * sSup ((fun z => ‖p.eval z‖) '' numericalRange T) := by
  sorry

/--
**Crouzeix–Palencia (2017): the numerical range is a `(1 + √2)`-spectral set.**

For every operator `T` on `ℂⁿ` and every polynomial `p`,
$$\|p(T)\| \le (1 + \sqrt{2}) \sup_{z \in W(T)} |p(z)|.$$

*Reference:* [CP17].
-/
@[category research solved, AMS 15 47]
theorem crouzeix_conjecture.variants.crouzeix_palencia {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ (1 + Real.sqrt 2) * sSup ((fun z => ‖p.eval z‖) '' numericalRange T) := by
  sorry

/--
**Crouzeix (2007): the numerical range is a `11.08`-spectral set.**

For every operator `T` on `ℂⁿ` and every polynomial `p`,
$$\|p(T)\| \le 11.08 \sup_{z \in W(T)} |p(z)|.$$

*Reference:* [Cr07].
-/
@[category research solved, AMS 15 47]
theorem crouzeix_conjecture.variants.crouzeix {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ 11.08 * sSup ((fun z => ‖p.eval z‖) '' numericalRange T) := by
  sorry

/--
**The `2 × 2` case (Crouzeix 2004).**

Crouzeix's conjecture holds for `2 × 2` matrices: for every operator `T` on `ℂ²` and every
polynomial `p`, $\|p(T)\| \le 2 \sup_{z \in W(T)} |p(z)|$.

*Reference:* [Cr04].
-/
@[category research solved, AMS 15 47]
theorem crouzeix_conjecture.variants.two_by_two
    (T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ 2 * sSup ((fun z => ‖p.eval z‖) '' numericalRange T) := by
  sorry

/-- The nilpotent shift `(x₀, x₁) ↦ (x₁, 0)` on `ℂ²`, i.e. the matrix `!![0, 1; 0, 0]`. -/
noncomputable def shift : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => EuclideanSpace.single 0 (x 1)
      map_add' := fun x y => by
        ext j
        by_cases hj : j = 0 <;> simp [hj]
      map_smul' := fun c x => by
        ext j
        simp [PiLp.single_apply] }

@[category API, AMS 15 47, simp]
lemma shift_apply (x : EuclideanSpace ℂ (Fin 2)) :
    shift x = EuclideanSpace.single 0 (x 1) := rfl

/-- Every element of the numerical range of the shift has absolute value at most `1 / 2`. -/
@[category API, AMS 15 47]
lemma norm_le_half_of_mem_numericalRange_shift {z : ℂ} (hz : z ∈ numericalRange shift) :
    ‖z‖ ≤ 1 / 2 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hinner : ⟪x, shift x⟫ = x 1 * (starRingEnd ℂ) (x 0) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, PiLp.single_apply]
  have hnorm : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq x
    rw [hx] at h
    simpa [Fin.sum_univ_two] using h.symm
  rw [hinner]
  have : ‖x 1 * (starRingEnd ℂ) (x 0)‖ = ‖x 1‖ * ‖x 0‖ := by
    rw [norm_mul, RCLike.norm_conj]
  rw [this]
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]

/--
**The constant `2` would be optimal.**

Any constant `C` for which $\|p(T)\| \le C \sup_{z \in W(T)} |p(z)|$ holds for all operators
and polynomials satisfies `2 ≤ C`. The witness is the nilpotent shift `T = !![0, 1; 0, 0]`
with `p = X`: its operator norm is `1` while its numerical range is the disc of radius `1 / 2`.
-/
@[category test, AMS 15 47]
theorem crouzeix_conjecture.variants.sharp (C : ℝ)
    (hC : ∀ (n : ℕ) (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (p : ℂ[X]),
      ‖aeval T p‖ ≤ C * sSup ((fun z => ‖p.eval z‖) '' numericalRange T)) :
    2 ≤ C := by
  set s : ℝ := sSup ((fun z => ‖z‖) '' numericalRange shift) with hs_def
  -- The numerical range of the shift lies in the disc of radius `1 / 2`.
  have hs_half : s ≤ 1 / 2 := by
    refine Real.sSup_le ?_ (by norm_num)
    rintro r ⟨z, hz, rfl⟩
    exact norm_le_half_of_mem_numericalRange_shift hz
  have hs_nonneg : 0 ≤ s :=
    Real.sSup_nonneg fun r hr => by
      obtain ⟨z, -, rfl⟩ := hr
      exact norm_nonneg z
  -- The operator norm of the shift is at least `1`.
  have h_norm : (1 : ℝ) ≤ ‖aeval shift (X : ℂ[X])‖ := by
    rw [aeval_X]
    have h := shift.le_opNorm (EuclideanSpace.single 1 (1 : ℂ))
    rw [shift_apply] at h
    simpa [PiLp.norm_single, PiLp.single_apply] using h
  -- Instantiate the hypothesis at the shift and `p = X`.
  have h_ineq := hC 2 shift X
  simp only [eval_X] at h_ineq
  rw [← hs_def] at h_ineq
  have h1 : (1 : ℝ) ≤ C * s := h_norm.trans h_ineq
  have hC_nonneg : 0 ≤ C := by
    by_contra h
    push Not at h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs_half hC_nonneg]

end CrouzeixConjecture
