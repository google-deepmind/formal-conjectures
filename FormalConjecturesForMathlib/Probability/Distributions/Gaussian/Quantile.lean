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

public import FormalConjecturesForMathlib.Probability.Quantile
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standard normal critical values

The standard normal critical value is the interior lower quantile of Mathlib's Gaussian law
with mean zero and variance one. Its CDF is continuous and strictly increasing, so the critical
value is the unique real point at which the CDF equals the given probability.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

/-- The standard normal CDF is continuous. -/
lemma continuous_cdf_standardNormal : Continuous (cdf (gaussianReal 0 1)) := by
  let :=  nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact continuous_cdf _

/-- The standard normal CDF is strictly increasing. -/
lemma strictMono_cdf_standardNormal : StrictMono (cdf (gaussianReal 0 1)) := by
  intro x y hxy
  have hpos : 0 < gaussianReal 0 1 (Ioc x y) := by
    apply pos_iff_ne_zero.2
    intro hz
    have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero hz
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hv
    exact (not_le_of_gt (sub_pos.2 hxy)) hv
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc] at hpos
  exact sub_pos.1 (ENNReal.ofReal_pos.1 hpos)

/-- The critical value for an interior probability under the standard normal law. -/
noncomputable def standardNormalQuantile (p : Ioo (0 : ℝ) 1) : ℝ :=
  lowerQuantile (gaussianReal 0 1) p

/-- A standard normal critical value has exactly the specified cumulative probability. -/
lemma cdf_standardNormalQuantile (p : Ioo (0 : ℝ) 1) :
    cdf (gaussianReal 0 1) (standardNormalQuantile p) = p.1 :=
  cdf_lowerQuantile_eq _ _ continuous_cdf_standardNormal.continuousAt

/-- A standard normal critical value is the unique point with its cumulative probability. -/
lemma standardNormalQuantile_eq_iff (p : Ioo (0 : ℝ) 1) (x : ℝ) :
    standardNormalQuantile p = x ↔ cdf (gaussianReal 0 1) x = p.1 := by
  constructor
  · rintro rfl
    exact cdf_standardNormalQuantile p
  · intro hx
    exact strictMono_cdf_standardNormal.injective ((cdf_standardNormalQuantile p).trans hx.symm)

/-- Standard normal critical values increase strictly with the probability. -/
lemma strictMono_standardNormalQuantile : StrictMono standardNormalQuantile := by
  intro p q hpq
  apply (strictMono_cdf_standardNormal.lt_iff_lt).1
  simpa only [cdf_standardNormalQuantile] using (show p.1 < q.1 from hpq)

/-- Reflection changes the standard normal cumulative probability to its complement. -/
lemma cdf_standardNormal_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (v := 1) one_ne_zero
  have hneg : ((gaussianReal 0 1).map (fun y ↦ -y)).real (Iic (-x)) =
      (gaussianReal 0 1).real (Ici x) := by
    rw [map_measureReal_apply measurable_neg measurableSet_Iic]
    congr 1
    ext y
    simp
  rw [gaussianReal_map_neg, neg_zero] at hneg
  have hsum := measureReal_union_add_inter (μ := gaussianReal 0 1)
    (s := Iic x) (t := Ici x) measurableSet_Ici
  have hinter : Iic x ∩ Ici x = {x} := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_singleton_iff]
    exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩
  simp only [Iic_union_Ici, hinter, measureReal_def, measure_univ, ENNReal.toReal_one,
    measure_singleton, ENNReal.toReal_zero, add_zero] at hsum
  rw [cdf_eq_real, cdf_eq_real, hneg]
  simp only [measureReal_def]
  linarith

/-- Reflection negates a standard normal critical value. -/
lemma standardNormalQuantile_compl (p : Ioo (0 : ℝ) 1) :
    standardNormalQuantile ⟨1 - p.1, by constructor <;> linarith [p.2.1, p.2.2]⟩ =
      -standardNormalQuantile p := by
  apply (standardNormalQuantile_eq_iff _ _).2
  rw [cdf_standardNormal_neg, cdf_standardNormalQuantile]

/-- The standard normal median is zero. -/
@[simp] lemma standardNormalQuantile_half :
    standardNormalQuantile ⟨1 / 2, by constructor <;> norm_num⟩ = 0 := by
  have h := standardNormalQuantile_compl ⟨1 / 2, by constructor <;> norm_num⟩
  norm_num at h
  linarith

end ProbabilityTheory
