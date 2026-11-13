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

public import FormalConjecturesForMathlib.Probability.Distributions.Gaussian.Quantile

/-!
# Bias-aware confidence intervals and uniform asymptotic coverage

The radius adds a worst-case bias allowance to the normal critical value times a standard error.
The significance level belongs to $(0,1)$. `UniformAsymptoticCoverage` expresses a lower bound
on the limiting coverage uniformly over an indexed family of laws, using the actual coverage
events. Both the sample space and the law index may vary with sample size.

## References

* T. Armstrong, M. Weidner, and A. Zeleneev,
  [*Robust Estimation and Inference in Panels with Interactive Fixed Effects*]
  (https://arxiv.org/abs/2210.06639v4), equations (10), (12), and Theorem 4.
-/

@[expose] public section

open MeasureTheory Filter Set ProbabilityTheory

namespace Statistics

/-- The exact standard-normal critical value for a two-sided level-$\alpha$ interval. -/
noncomputable def normalTwoSidedCritical (α : Ioo (0 : ℝ) 1) : ℝ :=
  standardNormalQuantile ⟨1 - α.1 / 2, by constructor <;> linarith [α.2.1, α.2.2]⟩

lemma cdf_normalTwoSidedCritical (α : Ioo (0 : ℝ) 1) :
    cdf (gaussianReal 0 1) (normalTwoSidedCritical α) = 1 - α.1 / 2 :=
  cdf_standardNormalQuantile _

lemma normalTwoSidedCritical_pos (α : Ioo (0 : ℝ) 1) : 0 < normalTwoSidedCritical α := by
  have hprob : (⟨1 / 2, by constructor <;> norm_num⟩ : Ioo (0 : ℝ) 1) <
      ⟨1 - α.1 / 2, by constructor <;> linarith [α.2.1, α.2.2]⟩ := by
    change 1 / 2 < 1 - α.1 / 2
    linarith [α.2.2]
  have hcrit := strictMono_standardNormalQuantile hprob
  rw [standardNormalQuantile_half] at hcrit
  exact hcrit

/-- The bias allowance times its sensitivity plus the normal sampling-error radius. -/
noncomputable def biasAwareRadius (allowance sensitivity se : ℝ) (α : Ioo (0 : ℝ) 1) : ℝ :=
  allowance * sensitivity + normalTwoSidedCritical α * se

/-- The closed interval centered at the estimate, with the bias-aware radius. -/
noncomputable def biasAwareInterval (center allowance sensitivity se : ℝ)
    (α : Ioo (0 : ℝ) 1) : Set ℝ :=
  Icc (center - biasAwareRadius allowance sensitivity se α)
    (center + biasAwareRadius allowance sensitivity se α)

lemma biasAwareRadius_nonneg {allowance sensitivity se : ℝ} (ha : 0 ≤ allowance)
    (hs : 0 ≤ sensitivity) (hse : 0 ≤ se) (α : Ioo (0 : ℝ) 1) :
    0 ≤ biasAwareRadius allowance sensitivity se α :=
  add_nonneg (mul_nonneg ha hs) (mul_nonneg (normalTwoSidedCritical_pos α).le hse)

lemma mem_biasAwareInterval_iff (center allowance sensitivity se target : ℝ)
    (α : Ioo (0 : ℝ) 1) :
    target ∈ biasAwareInterval center allowance sensitivity se α ↔
      |target - center| ≤ biasAwareRadius allowance sensitivity se α := by
  rw [biasAwareInterval, mem_Icc, abs_le]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

lemma center_mem_biasAwareInterval (center : ℝ) {allowance sensitivity se : ℝ}
    (ha : 0 ≤ allowance) (hs : 0 ≤ sensitivity) (hse : 0 ≤ se) (α : Ioo (0 : ℝ) 1) :
    center ∈ biasAwareInterval center allowance sensitivity se α := by
  rw [mem_biasAwareInterval_iff]
  simpa using biasAwareRadius_nonneg ha hs hse α

/-- Increasing the nonnegative bias allowance enlarges the interval. -/
lemma biasAwareInterval_mono_allowance (center se : ℝ) {a b sensitivity : ℝ}
    (hab : a ≤ b) (hs : 0 ≤ sensitivity) (α : Ioo (0 : ℝ) 1) :
    biasAwareInterval center a sensitivity se α ⊆ biasAwareInterval center b sensitivity se α := by
  intro target ht
  rw [mem_biasAwareInterval_iff] at ht ⊢
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_right hab hs) le_rfl)

/-- A zero bias allowance gives the ordinary normal interval, without asserting zero error. -/
@[simp] lemma biasAwareInterval_zero_allowance (center sensitivity se : ℝ)
    (α : Ioo (0 : ℝ) 1) :
    biasAwareInterval center 0 sensitivity se α =
      Icc (center - normalTwoSidedCritical α * se) (center + normalTwoSidedCritical α * se) := by
  simp [biasAwareInterval, biasAwareRadius]

variable {Θ Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- A uniform lower bound on asymptotic coverage for varying sample spaces and law families. -/
def UniformAsymptoticCoverage (μ : ∀ n, Θ n → Measure (Ω n))
    (target : ∀ n, Θ n → ℝ) (interval : ∀ n, Θ n → Ω n → Set ℝ) (level : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ θ,
    ENNReal.ofReal (level - ε) ≤ μ n θ {ω | target n θ ∈ interval n θ ω}

/-- Pointwise enlargement of every interval preserves the uniform coverage bound. -/
lemma UniformAsymptoticCoverage.mono {μ : ∀ n, Θ n → Measure (Ω n)}
    {target : ∀ n, Θ n → ℝ} {interval larger : ∀ n, Θ n → Ω n → Set ℝ} {level : ℝ}
    (h : UniformAsymptoticCoverage μ target interval level)
    (hsub : ∀ n θ ω, interval n θ ω ⊆ larger n θ ω) :
    UniformAsymptoticCoverage μ target larger level := by
  intro ε hε
  filter_upwards [h ε hε] with n hn θ
  exact (hn θ).trans (measure_mono fun ω hω ↦ hsub n θ ω hω)

/-- Uniform coverage at a level implies coverage at any smaller level. -/
lemma UniformAsymptoticCoverage.mono_level {μ : ∀ n, Θ n → Measure (Ω n)}
    {target : ∀ n, Θ n → ℝ} {interval : ∀ n, Θ n → Ω n → Set ℝ} {a b : ℝ}
    (h : UniformAsymptoticCoverage μ target interval b) (hab : a ≤ b) :
    UniformAsymptoticCoverage μ target interval a := by
  intro ε hε
  filter_upwards [h ε hε] with n hn θ
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hab ε)).trans (hn θ)

/-- An interval containing the target for every sample has uniform coverage one. -/
lemma uniformAsymptoticCoverage_of_forall_mem (μ : ∀ n, Θ n → Measure (Ω n))
    [hlaws : ∀ n θ, IsProbabilityMeasure (μ n θ)] (target : ∀ n, Θ n → ℝ)
    (interval : ∀ n, Θ n → Ω n → Set ℝ) (hmem : ∀ n θ ω, target n θ ∈ interval n θ ω) :
    UniformAsymptoticCoverage μ target interval 1 := by
  intro ε hε
  filter_upwards [] with n θ
  have := hlaws n θ
  have hevent : {ω | target n θ ∈ interval n θ ω} = univ := by
    ext ω
    simp [hmem n θ ω]
  rw [hevent, measure_univ]
  exact (ENNReal.ofReal_le_ofReal (by linarith : 1 - ε ≤ 1)).trans (by simp)

end Statistics
