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
# The Kannan--Lovász--Simonovits inequality

The dimension-free Poincaré bound for isotropic log-concave probability densities,
on the locally Lipschitz $L^2$ test class of Bizeul–Klartag–Lehec, Theorem 1.1.
The squared-gradient energy is an extended nonnegative integral and may be infinite.

*References:*
- [BKL26] Pierre Bizeul, Boaz Klartag and Joseph Lehec,
  *Presenting a proof of the Kannan-Lovász-Simonovits conjecture*,
  [arXiv:2610.05474v1](https://arxiv.org/abs/2610.05474v1), Theorem 1.1.
- The ordinary density and isotropy definitions are adapted from
  [OpenAI's KLS model](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/KLS/Model.lean)
  (Apache-2.0).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace KannanLovaszSimonovits

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordinary Lebesgue-density measure. -/
def densityMeasure {n : ℕ} (ρ : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Probability-density and log-concavity conditions.
`ConcaveOn` includes convexity of the positive support. -/
structure IsLogConcaveDensity {n : ℕ} (ρ : Space n → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ ρ x
  measurable : Measurable ρ
  probability : IsProbabilityMeasure (densityMeasure ρ)
  log_concave : ConcaveOn ℝ {x | 0 < ρ x} (fun x => Real.log (ρ x))

/-- Zero mean and identity covariance, with all moment integrability explicit. -/
structure IsIsotropic {n : ℕ} (μ : Measure (Space n)) : Prop where
  integrable_coordinate : ∀ i : Fin n, Integrable (fun x : Space n => x i) μ
  integrable_product : ∀ i j : Fin n, Integrable (fun x : Space n => x i * x j) μ
  mean_zero : ∀ i : Fin n, (∫ x : Space n, x i ∂μ) = 0
  second_moment : ∀ i j : Fin n,
    (∫ x : Space n, x i * x j ∂μ) = if i = j then 1 else 0

def expectation {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, (f x - expectation μ f) ^ 2 ∂μ

/-- The squared-gradient energy, including infinite energy. -/
def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ENNReal :=
  ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂μ

/-- The locally Lipschitz $L^2(\mu)$ test class from the source theorem. -/
def IsTestFunction {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : Prop :=
  LocallyLipschitz f ∧ MemLp f 2 μ

/-- Direct Poincare inequality, avoiding an infimum convention for the constant. -/
def PoincareBound {n : ℕ} (μ : Measure (Space n)) (C : ℝ) : Prop :=
  ∀ f : Space n → ℝ, IsTestFunction μ f →
    ENNReal.ofReal (variance μ f) ≤ ENNReal.ofReal C * dirichletEnergy μ f

/-- The Kannan--Lovász--Simonovits inequality: one $C > 0$ bounds the Poincaré inequality
for every isotropic log-concave probability density on $\mathbb{R}^n$, every $n \geq 1$,
and every locally Lipschitz $L^2$ function. -/
@[category research solved, AMS 46 52 60]
theorem kannan_lovasz_simonovits :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
        PoincareBound (densityMeasure ρ) C := by
  sorry

/-- The zero function belongs to the stated test class. -/
@[category test, AMS 46 52 60]
theorem isTestFunction_zero {n : ℕ} (μ : Measure (Space n)) :
    IsTestFunction μ (fun _ : Space n => (0 : ℝ)) := by
  constructor
  · exact (LipschitzWith.const 0).locallyLipschitz
  · exact MemLp.zero'

/-- Isotropy supplies a nonsmooth, noncompactly supported test: an absolute coordinate. -/
@[category test, AMS 46 52 60]
theorem isTestFunction_abs_coordinate {n : ℕ} {μ : Measure (Space n)} (h : IsIsotropic μ)
    (i : Fin n) : IsTestFunction μ (fun x => |x i|) := by
  constructor
  · simpa [Function.comp_def, Real.norm_eq_abs] using
      (lipschitzWith_one_norm.comp (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitz).locallyLipschitz
  · have hm : AEStronglyMeasurable (fun x : Space n => x i) μ := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aestronglyMeasurable (μ := μ)
    have hL2 : MemLp (fun x : Space n => x i) 2 μ :=
      (memLp_two_iff_integrable_sq hm).mpr (by simpa only [pow_two] using h.integrable_product i i)
    simpa only [Real.norm_eq_abs] using hL2.norm

/-- Infinite squared-gradient energy is allowed and makes a positive-constant bound automatic. -/
@[category test, AMS 46 52 60]
theorem variance_le_of_infinite_energy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) {C : ℝ} (hC : 0 < C) (hE : dirichletEnergy μ f = ⊤) :
    ENNReal.ofReal (variance μ f) ≤ ENNReal.ofReal C * dirichletEnergy μ f := by
  rw [hE, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
  exact le_top

/-- The variance of the zero function is zero, including for a measure of infinite mass. -/
@[category test, AMS 46 52 60]
theorem variance_zero {n : ℕ} (μ : Measure (Space n)) :
    variance μ (fun _ => 0) = 0 := by
  simp [variance, expectation]

/-- Isotropy normalizes the variance of each coordinate to one. -/
@[category test, AMS 46 52 60]
theorem variance_coordinate {n : ℕ} {μ : Measure (Space n)} (h : IsIsotropic μ)
    (i : Fin n) : variance μ (fun x => x i) = 1 := by
  simpa [variance, expectation, h.mean_zero, pow_two] using h.second_moment i i

end KannanLovaszSimonovits
