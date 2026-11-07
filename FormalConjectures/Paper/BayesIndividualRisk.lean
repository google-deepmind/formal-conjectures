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
# Individual Bayes risk: COLT 2011 Question 2

Does every well-specified countable iid Bayes model admit a positive
polynomial rate for individual expected KL risk?

References:
- [GK11] P. D. Grünwald and W. Kotłowski,
  *Open Problem: Bounds on Individual Risk for Log-loss Predictors*,
  COLT 2011, PMLR 19:813–816, p.814, Question 2.
  https://proceedings.mlr.press/v19/grunwald11b/grunwald11b.pdf
- [Ki26] K. Kitamura, *Individual Bayes risk without polynomial convergence*,
  Lean 4 formalization (2026),
  [proof repository](https://github.com/KitaKen1/bayes-no-polynomial-rate-lean/tree/179e0a57c26d5b830afa23caeab84287243b9eaa).
-/

@[expose] public section

namespace BayesIndividualRisk

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

/-- A density model containing the true density 1, with a positive prior. -/
structure DensityModel (I Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) where
  density : I → Ω → ℝ
  measurable : ∀ i, Measurable (density i)
  nonneg : ∀ i x, 0 ≤ density i x
  integrable : ∀ i, Integrable (density i) P
  normalized : ∀ i, ∫ x, density i x ∂P = 1
  prior : I → ℝ
  prior_positive : ∀ i, 0 < prior i
  prior_sum : HasSum prior 1
  trueIndex : I
  true_density : ∀ x, density trueIndex x = 1

/-- The ordinary posterior predictive law after n observations. -/
noncomputable def DensityModel.predictionLaw {I Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (M : DensityModel I Ω P) (n : ℕ) (x : Fin n → Ω) : Measure Ω :=
  let L := fun i => ∏ t, M.density i (x t)
  let Z := ∑' i, M.prior i * L i
  P.withDensity (fun y => ENNReal.ofReal
    (if Z = 0 then 1 else (∑' i, M.prior i * L i * M.density i y) / Z))

/-- The expected individual KL risk after n iid observations. -/
noncomputable def DensityModel.risk {I Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (M : DensityModel I Ω P) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → Ω, klDiv P (M.predictionLaw n x) ∂Measure.pi (fun _ => P)

set_option linter.style.formal_proof_palomar false in
/-- Does every well-specified countable iid Bayes model admit a positive
polynomial individual-risk rate [GK11, Question 2]? The answer is no [Ki26]. -/
@[category research solved, question, AMS 60 62 68,
    formal_proof using lean4 at "https://github.com/KitaKen1/bayes-no-polynomial-rate-lean/blob/179e0a57c26d5b830afa23caeab84287243b9eaa/lean/BayesNoRate/FCPresentation.lean#L13"]
theorem polynomial_individual_risk :
    ¬ ∀ (I Ω : Type) [Countable I] [Infinite I] [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (M : DensityModel I Ω P),
      ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n ≥ max N 1,
          ENNReal.ofReal ((n : ℝ)^γ) * M.risk n ≤ ENNReal.ofReal C := by
  sorry

end BayesIndividualRisk
