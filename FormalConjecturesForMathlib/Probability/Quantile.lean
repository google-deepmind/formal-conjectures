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

public import Mathlib.Probability.CDF

/-!
# Interior quantiles of real probability laws

The lower quantile is the infimum of the points where the cumulative distribution function
reaches a given probability in $(0,1)$. The defining set is nonempty and bounded below.
The CDF need not equal the probability at a quantile: the law may have atoms.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace ProbabilityTheory

variable (μ : Measure ℝ) (p : Ioo (0 : ℝ) 1)

/-- The CDF reaches every interior probability at some finite point. -/
lemma lowerQuantile_set_nonempty : {x : ℝ | p.1 ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt p.2.2).exists
  exact ⟨x, hx.le⟩

/-- The points where the CDF reaches an interior probability are bounded below. -/
lemma lowerQuantile_set_bddBelow : BddBelow {x : ℝ | p.1 ≤ cdf μ x} := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const p.2.1).exists
  refine ⟨a, fun x hx ↦ ?_⟩
  by_contra h
  exact (not_le_of_gt ha) (hx.trans ((monotone_cdf μ) (le_of_not_ge h)))

/-- The lower quantile of a real probability law, at an interior probability. -/
noncomputable def lowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : Ioo (0 : ℝ) 1) : ℝ := sInf {x : ℝ | p.1 ≤ cdf μ x}

variable [IsProbabilityMeasure μ]

/-- The lower quantile lies below each point whose CDF reaches the given probability. -/
lemma lowerQuantile_le_of_le_cdf {x : ℝ} (hx : p.1 ≤ cdf μ x) :
    lowerQuantile μ p ≤ x :=
  csInf_le (lowerQuantile_set_bddBelow μ p) hx

/-- The CDF at the lower quantile reaches the specified probability, including at atoms. -/
lemma le_cdf_lowerQuantile : p.1 ≤ cdf μ (lowerQuantile μ p) := by
  rw [← (cdf μ).iInf_Ioi_eq]
  refine le_ciInf fun x ↦ ?_
  obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (lowerQuantile_set_nonempty μ p) x.2
  exact hy.trans ((monotone_cdf μ) hyx.le)

/-- The defining order characterization of a lower quantile. -/
lemma lowerQuantile_le_iff {x : ℝ} : lowerQuantile μ p ≤ x ↔ p.1 ≤ cdf μ x := by
  constructor
  · intro h
    exact (le_cdf_lowerQuantile μ p).trans ((monotone_cdf μ) h)
  · exact lowerQuantile_le_of_le_cdf μ p

/-- Every point strictly below a lower quantile has CDF strictly below the probability. -/
lemma lt_lowerQuantile_iff {x : ℝ} : x < lowerQuantile μ p ↔ cdf μ x < p.1 := by
  simpa only [not_le] using (not_congr (lowerQuantile_le_iff μ p (x := x)))

/-- A lower quantile is uniquely characterized by reaching the probability for the first time. -/
lemma lowerQuantile_eq_iff (x : ℝ) :
    lowerQuantile μ p = x ↔ p.1 ≤ cdf μ x ∧ ∀ y < x, cdf μ y < p.1 := by
  constructor
  · rintro rfl
    exact ⟨le_cdf_lowerQuantile μ p, fun y hy ↦ (lt_lowerQuantile_iff μ p).1 hy⟩
  · rintro ⟨hx, hlt⟩
    apply le_antisymm (lowerQuantile_le_of_le_cdf μ p hx)
    by_contra h
    exact (not_lt_of_ge (le_cdf_lowerQuantile μ p)) (hlt _ (lt_of_not_ge h))

/-- Lower quantiles increase with their probability argument. -/
lemma monotone_lowerQuantile : Monotone (lowerQuantile μ) := by
  intro p q hpq
  exact (lowerQuantile_le_iff μ p).2
    ((show p.1 ≤ q.1 from hpq).trans (le_cdf_lowerQuantile μ q))

/-- Continuity at a lower quantile rules out overshooting its probability. -/
lemma cdf_lowerQuantile_eq (h : ContinuousAt (cdf μ) (lowerQuantile μ p)) :
    cdf μ (lowerQuantile μ p) = p.1 := by
  apply le_antisymm _ (le_cdf_lowerQuantile μ p)
  apply le_of_tendsto (h.continuousWithinAt (s := Iio (lowerQuantile μ p)))
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((lt_lowerQuantile_iff μ p).1 hx).le

/-- A point mass has its location as every interior lower quantile. -/
@[simp] lemma lowerQuantile_dirac (a : ℝ) : lowerQuantile (Measure.dirac a) p = a := by
  apply le_antisymm
  · apply lowerQuantile_le_of_le_cdf
    simpa [cdf_eq_real, measureReal_def] using p.2.2.le
  · by_contra h
    have hlt : lowerQuantile (Measure.dirac a) p < a := lt_of_not_ge h
    have hzero : cdf (Measure.dirac a) (lowerQuantile (Measure.dirac a) p) = 0 := by
      simp [cdf_eq_real, measureReal_def, hlt.not_ge]
    have := le_cdf_lowerQuantile (Measure.dirac a) p
    rw [hzero] at this
    exact (not_le_of_gt p.2.1) this

/-- The CDF overshoots every interior probability at a point mass's quantile. -/
lemma cdf_lowerQuantile_dirac (a : ℝ) :
    cdf (Measure.dirac a) (lowerQuantile (Measure.dirac a) p) = 1 := by
  simp [cdf_eq_real, measureReal_def]

/-- A real probability law without atoms has a continuous CDF. -/
lemma continuous_cdf [NullSingletonClass μ] : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.2
  rw [(cdf μ).rightLim_eq]
  apply le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
  have hzero : ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, measure_singleton]
  exact sub_nonpos.1 (ENNReal.ofReal_eq_zero.1 hzero)

end ProbabilityTheory
