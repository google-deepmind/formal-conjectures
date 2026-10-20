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

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.ComputeDegree

@[expose] public section
/-!
# Pisot–Vijayaraghavan numbers

A *Pisot–Vijayaraghavan number* (or *PV number*) is a real algebraic integer
`θ > 1` all of whose Galois conjugates other than `θ` itself lie strictly
inside the complex unit disc. Equivalently, every root in `ℂ` of the minimal
polynomial of `θ` over `ℚ`, apart from `θ`, has modulus `< 1`.

*References*:
- [Wikipedia, Pisot–Vijayaraghavan number](https://en.wikipedia.org/wiki/Pisot%E2%80%93Vijayaraghavan_number)

## Main definitions

* `IsPisot`: a real number is a Pisot–Vijayaraghavan number.

## Main statements

* `isPisot_goldenRatio`: the golden ratio is a Pisot number.

-/

open Polynomial

/-- A **Pisot–Vijayaraghavan number** is a real algebraic integer `θ > 1` all of
whose other conjugates lie strictly inside the complex unit disc: every root in
`ℂ` of the minimal polynomial of `θ` over `ℚ`, except `θ` itself, has
modulus `< 1`. -/
def IsPisot (θ : ℝ) : Prop :=
  1 < θ ∧ IsIntegral ℤ θ ∧ ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1

open Real in
/-- The golden ratio `φ = (1 + √5) / 2` is a Pisot number: it is an algebraic
integer greater than `1`, its minimal polynomial over `ℚ` is `X ^ 2 - X - 1`, and
its only other conjugate `ψ = (1 - √5) / 2` has modulus `(√5 - 1) / 2 < 1`. -/
theorem isPisot_goldenRatio : IsPisot goldenRatio := by
  refine ⟨one_lt_goldenRatio, ?_, ?_⟩
  · -- `φ` is an algebraic integer: a root of the monic `X ^ 2 - X - 1 ∈ ℤ[X]`.
    refine ⟨X ^ 2 - X - 1, by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_sub, map_pow, map_one, aeval_X]
    linarith [goldenRatio_sq]
  · -- Every complex root of `minpoly ℚ φ` other than `φ` is the conjugate `ψ`.
    intro z hz hzφ
    rw [Polynomial.mem_aroots'] at hz
    -- `minpoly ℚ φ ∣ X ^ 2 - X - 1`, so `z` is a root of `X ^ 2 - X - 1` as well.
    have hdvd : minpoly ℚ goldenRatio ∣ (X ^ 2 - X - 1 : ℚ[X]) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, map_one, aeval_X]
      linarith [goldenRatio_sq]
    obtain ⟨g, hg⟩ := hdvd
    have hquad : z ^ 2 - z - 1 = 0 := by
      have hz1 : (aeval z) (X ^ 2 - X - 1 : ℚ[X]) = 0 := by
        rw [hg, map_mul, hz.2, zero_mul]
      simpa only [map_sub, map_pow, map_one, aeval_X] using hz1
    -- `X ^ 2 - X - 1 = (X - φ)(X - ψ)`, using `φ + ψ = 1` and `φ * ψ = -1`.
    have hsum : (goldenRatio : ℂ) + (goldenConj : ℂ) = 1 := by
      rw [← Complex.ofReal_add, goldenRatio_add_goldenConj]; norm_num
    have hprod : (goldenRatio : ℂ) * (goldenConj : ℂ) = -1 := by
      rw [← Complex.ofReal_mul, goldenRatio_mul_goldenConj]; norm_num
    have hfac : (z - (goldenRatio : ℂ)) * (z - (goldenConj : ℂ)) = 0 := by
      linear_combination hquad - z * hsum + hprod
    -- Hence `z = ψ`, whose modulus is `< 1`.
    have hzψ : z = (goldenConj : ℂ) := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hzφ
      · exact sub_eq_zero.mp h
    rw [hzψ, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
