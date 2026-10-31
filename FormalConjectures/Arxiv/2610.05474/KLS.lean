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

The smooth compactly supported test-function formulation of the dimension-free
Poincaré bound for isotropic log-concave probability densities.

*References:*
- [BKL26] Pierre Bizeul, Boaz Klartag and Joseph Lehec,
  *Presenting a proof of the Kannan-Lovász-Simonovits conjecture*,
  [arXiv:2610.05474v1](https://arxiv.org/abs/2610.05474v1), Theorem 1.1.
- The ordinary density, isotropy and test-function definitions are adapted from
  [OpenAI's KLS model](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/KLS/Model.lean)
  (Apache-2.0).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

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

def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The exact compactly supported smooth real test-function class. -/
def IsTestFunction {n : ℕ} (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- Direct Poincare inequality, avoiding an infimum convention for the constant. -/
def PoincareBound {n : ℕ} (μ : Measure (Space n)) (C : ℝ) : Prop :=
  ∀ f : Space n → ℝ, IsTestFunction f → variance μ f ≤ C * dirichletEnergy μ f

/-- The Kannan--Lovász--Simonovits inequality in its smooth compactly supported test-function
formulation: one $C > 0$ bounds the Poincaré inequality for every isotropic log-concave
probability density on $\mathbb{R}^n$, for every $n \geq 1$. -/
@[category research solved, AMS 46 52 60]
theorem kannan_lovasz_simonovits :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
        PoincareBound (densityMeasure ρ) C := by
  sorry

/-- The zero function belongs to the stated test class. -/
@[category test, AMS 46 52 60]
theorem isTestFunction_zero (n : ℕ) : IsTestFunction (fun _ : Space n => (0 : ℝ)) := by
  constructor
  · exact contDiff_const
  · simp [HasCompactSupport]

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
