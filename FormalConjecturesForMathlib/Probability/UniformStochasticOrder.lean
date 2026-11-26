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

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Uniform stochastic orders

The sample space and the index set of laws may depend on the sample-size index. These
definitions express uniform stochastic orders by actual tail probabilities. The bounds hold
eventually in sample size, uniformly in the law index. Applications use positive rate sequences.

`UniformAsymp` combines an upper-tail bound with a lower-tail bound. The lower-tail formulation
excludes a zero statistic and avoids the totalized value of its reciprocal at zero.

## References

* T. Armstrong, M. Weidner, and A. Zeleneev,
  [*Robust Estimation and Inference in Panels with Interactive Fixed Effects*]
  (https://arxiv.org/abs/2210.06639v4), §4.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Θ Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Uniform boundedness in probability at a deterministic rate. -/
def UniformOp (μ : ∀ n, Θ n → Measure (Ω n)) (X : ∀ n, Θ n → Ω n → ℝ)
    (rate : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, ∀ θ, μ n θ {ω | C * rate n ≤ |X n θ ω|} ≤ ENNReal.ofReal ε

/-- Uniform convergence to zero in probability after scaling by a deterministic rate. -/
def UniformLittleOp (μ : ∀ n, Θ n → Measure (Ω n)) (X : ∀ n, Θ n → Ω n → ℝ)
    (rate : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
    ∀ᶠ n in atTop, ∀ θ, μ n θ {ω | ε * rate n ≤ |X n θ ω|} ≤ ENNReal.ofReal η

/-- Uniform comparability in probability: bounded above and bounded away from zero at the rate. -/
def UniformAsymp (μ : ∀ n, Θ n → Measure (Ω n)) (X : ∀ n, Θ n → Ω n → ℝ)
    (rate : ℕ → ℝ) : Prop :=
  UniformOp μ X rate ∧ ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n in atTop, ∀ θ, μ n θ {ω | |X n θ ω| ≤ c * rate n} ≤ ENNReal.ofReal ε

/-- Events whose probabilities approach one uniformly over the family of laws. -/
def UniformHighProbability (μ : ∀ n, Θ n → Measure (Ω n))
    (events : ∀ n, Θ n → Set (Ω n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ θ, μ n θ (events n θ)ᶜ ≤ ENNReal.ofReal η

/-- Enlarging the events preserves uniform high probability. -/
lemma UniformHighProbability.mono {μ : ∀ n, Θ n → Measure (Ω n)}
    {events larger : ∀ n, Θ n → Set (Ω n)} (h : UniformHighProbability μ events)
    (hsub : ∀ n θ, events n θ ⊆ larger n θ) : UniformHighProbability μ larger := by
  intro η hη
  filter_upwards [h η hη] with n hn θ
  exact (measure_mono (Set.compl_subset_compl.2 (hsub n θ))).trans (hn θ)

/-- The certain event has uniform high probability. -/
lemma uniformHighProbability_univ (μ : ∀ n, Θ n → Measure (Ω n)) :
    UniformHighProbability μ (fun _ _ ↦ Set.univ) := by
  intro η hη
  filter_upwards [] with n θ
  simp

/-- Little-oh in probability implies boundedness in probability at the same rate. -/
lemma UniformLittleOp.uniformOp {μ : ∀ n, Θ n → Measure (Ω n)}
    {X : ∀ n, Θ n → Ω n → ℝ} {rate : ℕ → ℝ} (h : UniformLittleOp μ X rate) :
    UniformOp μ X rate := fun ε hε ↦ ⟨1, zero_lt_one, h 1 zero_lt_one ε hε⟩

/-- The zero statistic is uniformly little-oh of every positive rate. -/
lemma uniformLittleOp_zero (μ : ∀ n, Θ n → Measure (Ω n)) {rate : ℕ → ℝ}
    (hrate : ∀ n, 0 < rate n) : UniformLittleOp μ (fun _ _ _ ↦ 0) rate := by
  intro ε hε η hη
  filter_upwards [] with n θ
  have hpos : 0 < ε * rate n := mul_pos hε (hrate n)
  simp [not_le_of_gt hpos]

/-- A positive deterministic rate is comparable to itself, including for varying law families. -/
lemma uniformAsymp_rate (μ : ∀ n, Θ n → Measure (Ω n)) {rate : ℕ → ℝ}
    (hrate : ∀ n, 0 < rate n) : UniformAsymp μ (fun n _ _ ↦ rate n) rate := by
  constructor
  · intro ε hε
    refine ⟨2, by norm_num, Filter.Eventually.of_forall fun n θ ↦ ?_⟩
    have hlt : |rate n| < 2 * rate n := by rw [abs_of_pos (hrate n)]; linarith [hrate n]
    simp [not_le_of_gt hlt]
  · intro ε hε
    refine ⟨2⁻¹, by norm_num, Filter.Eventually.of_forall fun n θ ↦ ?_⟩
    have hlt : 2⁻¹ * rate n < |rate n| := by rw [abs_of_pos (hrate n)]; linarith [hrate n]
    simp [not_le_of_gt hlt]

/-- A zero statistic under genuine probability laws is not comparable to a positive rate. -/
lemma not_uniformAsymp_zero (μ : ∀ n, Θ n → Measure (Ω n))
    [hlaws : ∀ n θ, IsProbabilityMeasure (μ n θ)] [hΘ : ∀ n, Nonempty (Θ n)]
    {rate : ℕ → ℝ} (hrate : ∀ n, 0 < rate n) :
    ¬ UniformAsymp μ (fun _ _ _ ↦ 0) rate := by
  rintro ⟨_, h⟩
  obtain ⟨c, hc, hev⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨θ⟩ := hΘ n
  have := hlaws n θ
  have hbound := hn θ
  have hnonneg : (0 : ℝ) ≤ c * rate n := (mul_pos hc (hrate n)).le
  norm_num [hnonneg] at hbound

/-- With one fixed law, uniform little-oh at rate one is ordinary convergence in measure. -/
lemma uniformLittleOp_singleton_iff {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (X : ℕ → S → ℝ) :
    UniformLittleOp (Θ := fun _ ↦ Unit) (Ω := fun _ ↦ S) (fun _ _ ↦ μ)
      (fun n _ ↦ X n) (fun _ ↦ 1) ↔ TendstoInMeasure μ X atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm]
  constructor
  · intro h ε hε
    apply ENNReal.tendsto_nhds_zero.2
    intro η hη
    by_cases htop : η = ⊤
    · simp [htop]
    · have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
      filter_upwards [h ε hε η.toReal hηreal] with n hn
      simpa [ENNReal.ofReal_toReal htop, Real.norm_eq_abs] using hn ()
  · intro h ε hε η hη
    have hev := ENNReal.tendsto_nhds_zero.1 (h ε hε)
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
    filter_upwards [hev] with n hn θ
    simpa [Real.norm_eq_abs] using hn

end ProbabilityTheory
