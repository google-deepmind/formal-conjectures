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

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Multivariable logarithmic Mahler measure

Given $P \in \mathbb{C}[X_0, \dots, X_{n-1}]$, its logarithmic Mahler measure integrates
$\log \|P\|$ over the unit $n$-torus $\mathbb{T}^n \subseteq \mathbb{C}^n$. For $n = 1$, this
agrees with `Polynomial.logMahlerMeasure` under `MvPolynomial.uniqueAlgEquiv`.

*References:*
- [Wikipedia, Mahler measure](https://en.wikipedia.org/wiki/Mahler_measure)
-/

namespace MvPolynomial

open MeasureTheory

/-- Torus map $\theta \mapsto (e^{2\pi i \theta_0}, \dots, e^{2\pi i \theta_{n-1}})$ sending
$[0, 1]^n$ onto $\mathbb{T}^n \subseteq \mathbb{C}^n$. -/
noncomputable def torusPoint {n : ℕ} (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j ↦ Complex.exp (2 * Real.pi * θ j * Complex.I)

/-- Multivariable logarithmic Mahler integral
$m(P) = \int_{[0, 1]^n} \log \|P(e^{2\pi i \theta})\| \, d\theta$ for
$P \in \mathbb{C}[X_0, \dots, X_{n-1}]$. -/
noncomputable def logMahlerMeasure {n : ℕ} (P : MvPolynomial (Fin n) ℂ) : ℝ :=
  ∫ θ in Set.Icc (0 : Fin n → ℝ) 1, Real.log ‖eval (torusPoint θ) P‖

@[simp]
theorem norm_torusPoint {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) :
    ‖torusPoint θ j‖ = 1 := by
  unfold torusPoint
  have h := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * θ j)
  push_cast at h
  exact h

@[simp]
theorem logMahlerMeasure_C {n : ℕ} (c : ℂ) :
    logMahlerMeasure (C c : MvPolynomial (Fin n) ℂ) = Real.log ‖c‖ := by
  unfold logMahlerMeasure
  have h01 : (0 : Fin n → ℝ) ≤ 1 := fun _ ↦ zero_le_one
  simp [Measure.real, Real.volume_Icc_pi_toReal h01]

@[simp]
theorem logMahlerMeasure_monomial_one {n : ℕ} (d : Fin n →₀ ℕ) :
    logMahlerMeasure (monomial d (1 : ℂ)) = 0 := by
  unfold logMahlerMeasure
  have hnorm (θ : Fin n → ℝ) : ‖eval (torusPoint θ) (monomial d 1)‖ = 1 := by
    rw [eval_monomial, one_mul, Finsupp.prod, norm_prod]
    exact Finset.prod_eq_one fun j _ ↦ by rw [norm_pow, norm_torusPoint, one_pow]
  simp [hnorm]

private lemma eval_uniqueAlgEquiv_fin_one (P : MvPolynomial (Fin 1) ℂ) (z : ℂ) :
    Polynomial.eval z (uniqueAlgEquiv ℂ (Fin 1) P) = eval (fun _ ↦ z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp_all
  | mul_X f i ih =>
      rw [Subsingleton.elim i 0]
      simp_all

/-- In one variable (`Fin 1`), `MvPolynomial.logMahlerMeasure` agrees with Mathlib's
`Polynomial.logMahlerMeasure` under `MvPolynomial.uniqueAlgEquiv`. -/
theorem logMahlerMeasure_fin_one (P : MvPolynomial (Fin 1) ℂ) :
    logMahlerMeasure P = (uniqueAlgEquiv ℂ (Fin 1) P).logMahlerMeasure := by
  set p : Polynomial ℂ := uniqueAlgEquiv ℂ (Fin 1) P
  set g : ℝ → ℝ := fun x ↦ Real.log ‖Polynomial.eval (circleMap 0 1 x) p‖
  have hpre :
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Set.Icc (0 : ℝ) 1 =
        Set.Icc (0 : Fin 1 → ℝ) 1 := by
    ext θ
    simp [Pi.le_def]
  have hfun (θ : Fin 1 → ℝ) :
      Real.log ‖eval (torusPoint θ) P‖ =
        g (2 * Real.pi * MeasurableEquiv.funUnique (Fin 1) ℝ θ) := by
    have htor : torusPoint θ = fun _ ↦ circleMap 0 1 (2 * Real.pi * θ 0) := by
      ext j
      rw [Subsingleton.elim j 0]
      simp [torusPoint, circleMap]
    rw [htor, ← eval_uniqueAlgEquiv_fin_one]
    rfl
  unfold logMahlerMeasure
  simp_rw [hfun, ← hpre]
  trans ∫ t in Set.Icc (0 : ℝ) 1, g (2 * Real.pi * t)
  · exact MeasurePreserving.setIntegral_preimage_emb (volume_preserving_funUnique (Fin 1) ℝ)
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (fun t ↦ g (2 * Real.pi * t)) (Set.Icc 0 1)
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (zero_le_one' ℝ),
      intervalIntegral.integral_comp_mul_left g (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    simp [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, g]

@[simp]
theorem logMahlerMeasure_uniqueAlgEquiv_symm (p : Polynomial ℂ) :
    logMahlerMeasure ((uniqueAlgEquiv ℂ (Fin 1)).symm p) = p.logMahlerMeasure := by
  rw [logMahlerMeasure_fin_one, AlgEquiv.apply_symm_apply]

end MvPolynomial
