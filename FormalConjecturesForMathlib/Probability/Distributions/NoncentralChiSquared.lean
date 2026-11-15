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
public import Mathlib.Probability.Independence.Basic

/-!
# Noncentral chi-squared laws

The noncentral chi-squared law is the sum of the squares of independent Gaussian coordinates
with variance one. For positive dimension, the first coordinate has mean $\sqrt{\delta}$ and the
other coordinates have mean zero, so the noncentrality parameter is $\delta$. In dimension zero,
the sum is empty and its law is the point mass at zero, independently of the parameter.

## References

* C. L. Skeels and F. Windmeijer, *On the Stock–Yogo Tables*, Econometrics 6(4), 44 (2018),
  equations (5) and (8)–(10), https://doi.org/10.3390/econometrics6040044.
-/

@[expose] public section

open MeasureTheory Measure Set
open scoped BigOperators NNReal

namespace ProbabilityTheory

/-- The canonical mean vector for noncentrality `δ` in dimension `n`. -/
noncomputable def noncentralChiSquaredMean (n : ℕ) (δ : ℝ≥0) (i : Fin n) : ℝ :=
  if i.1 = 0 then Real.sqrt δ else 0

/-- Independent Gaussian coordinates defining the noncentral chi-squared law. -/
noncomputable def noncentralChiSquaredGaussian (n : ℕ) (δ : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (noncentralChiSquaredMean n δ i) 1

instance (n : ℕ) (δ : ℝ≥0) : IsProbabilityMeasure (noncentralChiSquaredGaussian n δ) := by
  unfold noncentralChiSquaredGaussian
  infer_instance

/-- The sum of coordinate squares. -/
def noncentralChiSquaredStatistic (n : ℕ) (z : Fin n → ℝ) : ℝ := ∑ i, z i ^ 2

@[fun_prop] lemma measurable_noncentralChiSquaredStatistic (n : ℕ) :
    Measurable (noncentralChiSquaredStatistic n) := by
  unfold noncentralChiSquaredStatistic
  fun_prop

lemma noncentralChiSquaredStatistic_nonneg (n : ℕ) (z : Fin n → ℝ) :
    0 ≤ noncentralChiSquaredStatistic n z :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The law of the squared length of the independent shifted standard normal coordinates. -/
noncomputable def noncentralChiSquared (n : ℕ) (δ : ℝ≥0) : Measure ℝ :=
  (noncentralChiSquaredGaussian n δ).map (noncentralChiSquaredStatistic n)

instance (n : ℕ) (δ : ℝ≥0) : IsProbabilityMeasure (noncentralChiSquared n δ) :=
  isProbabilityMeasure_map (measurable_noncentralChiSquaredStatistic n).aemeasurable

/-- The coordinates used in the construction are independent. -/
lemma iIndepFun_noncentralChiSquaredGaussian (n : ℕ) (δ : ℝ≥0) :
    iIndepFun (fun i (z : Fin n → ℝ) ↦ z i) (noncentralChiSquaredGaussian n δ) := by
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- Each coordinate has its specified shifted standard normal law. -/
lemma noncentralChiSquaredGaussian_map_eval (n : ℕ) (δ : ℝ≥0) (i : Fin n) :
    (noncentralChiSquaredGaussian n δ).map (Function.eval i) =
      gaussianReal (noncentralChiSquaredMean n δ i) 1 :=
  (measurePreserving_eval (fun j ↦ gaussianReal (noncentralChiSquaredMean n δ j) 1) i).map_eq

/-- The squared length of the mean vector is the noncentrality parameter in positive dimension. -/
lemma sum_sq_noncentralChiSquaredMean (n : ℕ) (δ : ℝ≥0) (hn : 0 < n) :
    ∑ i, noncentralChiSquaredMean n δ i ^ 2 = δ := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => simp [noncentralChiSquaredMean, Real.sq_sqrt]

/-- Splitting off the shifted coordinate expresses the law as a product pushforward. -/
lemma noncentralChiSquared_succ (n : ℕ) (δ : ℝ≥0) :
    noncentralChiSquared (n + 1) δ =
      ((gaussianReal (Real.sqrt δ) 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)).map
        (fun z ↦ z.1 ^ 2 + noncentralChiSquaredStatistic n z.2) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he := measurePreserving_piFinSuccAbove
    (fun i ↦ gaussianReal (noncentralChiSquaredMean (n + 1) δ i) 1) 0
  have hm : ((noncentralChiSquaredGaussian (n + 1) δ).map e) =
      (gaussianReal (Real.sqrt δ) 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    simpa [e, noncentralChiSquaredGaussian, noncentralChiSquaredMean] using he.map_eq
  rw [← hm, Measure.map_map (by fun_prop) e.measurable]
  rw [noncentralChiSquared]
  congr 1
  funext z
  simp [e, noncentralChiSquaredStatistic, Fin.sum_univ_succ, Fin.tail]

/-- Positive-dimensional noncentral chi-squared laws have no atoms. -/
lemma nullSingletonClass_noncentralChiSquared (n : ℕ) (δ : ℝ≥0) (hn : 0 < n) :
    NullSingletonClass (noncentralChiSquared n δ) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    let : NullSingletonClass (gaussianReal (Real.sqrt δ) 1) :=
      nullSingletonClass_gaussianReal one_ne_zero
    constructor
    intro t
    rw [noncentralChiSquared_succ,
      Measure.map_apply (by fun_prop) (measurableSet_singleton t),
      Measure.prod_apply_symm (measurableSet_singleton t |>.preimage (by fun_prop))]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro z
    apply measure_mono_null (t := {Real.sqrt (t - noncentralChiSquaredStatistic n z),
      -Real.sqrt (t - noncentralChiSquaredStatistic n z)})
    · intro a ha
      have heq : a ^ 2 + noncentralChiSquaredStatistic n z = t := ha
      have hsq : a ^ 2 = t - noncentralChiSquaredStatistic n z := by linarith
      have hnonneg : 0 ≤ t - noncentralChiSquaredStatistic n z := by
        rw [← hsq]
        exact sq_nonneg a
      have hroot : a ^ 2 = (Real.sqrt (t - noncentralChiSquaredStatistic n z)) ^ 2 := by
        rw [Real.sq_sqrt hnonneg, hsq]
      simpa only [mem_insert_iff, mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.1 hroot
    · exact (Set.toFinite _).measure_zero _

/-- The law is supported on the nonnegative real numbers. -/
lemma ae_nonneg_noncentralChiSquared (n : ℕ) (δ : ℝ≥0) :
    ∀ᵐ x ∂noncentralChiSquared n δ, 0 ≤ x := by
  rw [noncentralChiSquared, ae_map_iff (measurable_noncentralChiSquaredStatistic n).aemeasurable
    measurableSet_Ici]
  exact Filter.Eventually.of_forall (noncentralChiSquaredStatistic_nonneg n)

/-- Positive dimension gives no mass at or below zero. -/
lemma noncentralChiSquared_Iic_zero (n : ℕ) (δ : ℝ≥0) (hn : 0 < n) :
    noncentralChiSquared n δ (Iic 0) = 0 := by
  let i : Fin n := ⟨0, hn⟩
  let : NullSingletonClass (gaussianReal (noncentralChiSquaredMean n δ i) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  rw [noncentralChiSquared,
    Measure.map_apply (measurable_noncentralChiSquaredStatistic n) measurableSet_Iic]
  apply measure_mono_null (t := {z : Fin n → ℝ | z i = 0})
  · intro z hz
    have hzero : ∑ j, z j ^ 2 = 0 :=
      le_antisymm hz (noncentralChiSquaredStatistic_nonneg n z)
    have hi : z i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (z j))).1 hzero i (Finset.mem_univ i)
    exact sq_eq_zero_iff.1 hi
  · exact Measure.pi_hyperplane _ i 0

/-- Zero noncentrality gives unshifted standard normal coordinates. -/
@[simp] lemma noncentralChiSquared_zero_noncentrality (n : ℕ) :
    noncentralChiSquared n 0 =
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map (noncentralChiSquaredStatistic n) := by
  simp [noncentralChiSquared, noncentralChiSquaredGaussian, noncentralChiSquaredMean]

/-- The empty sum of squares has its point mass at zero. -/
@[simp] lemma noncentralChiSquared_zero_dim (δ : ℝ≥0) :
    noncentralChiSquared 0 δ = Measure.dirac 0 := by
  have h : noncentralChiSquaredStatistic 0 = fun _ ↦ 0 := by
    funext z
    simp [noncentralChiSquaredStatistic]
  rw [noncentralChiSquared, h, Measure.map_const, measure_univ, one_smul]

/-- An interior critical quantile of a noncentral chi-squared law. -/
noncomputable def noncentralChiSquaredQuantile (n : ℕ) (δ : ℝ≥0)
    (p : Ioo (0 : ℝ) 1) : ℝ :=
  lowerQuantile (noncentralChiSquared n δ) p

/-- Positive dimension makes the noncentral chi-squared CDF continuous. -/
lemma continuous_cdf_noncentralChiSquared (n : ℕ) (δ : ℝ≥0) (hn : 0 < n) :
    Continuous (cdf (noncentralChiSquared n δ)) := by
  let := nullSingletonClass_noncentralChiSquared n δ hn
  exact continuous_cdf _

/-- In positive dimension, a critical quantile has its specified cumulative probability. -/
lemma cdf_noncentralChiSquaredQuantile (n : ℕ) (δ : ℝ≥0) (p : Ioo (0 : ℝ) 1)
    (hn : 0 < n) : cdf (noncentralChiSquared n δ) (noncentralChiSquaredQuantile n δ p) = p.1 :=
  cdf_lowerQuantile_eq _ _ (continuous_cdf_noncentralChiSquared n δ hn).continuousAt

/-- Every interior critical quantile is positive in positive dimension. -/
lemma noncentralChiSquaredQuantile_pos (n : ℕ) (δ : ℝ≥0) (p : Ioo (0 : ℝ) 1)
    (hn : 0 < n) : 0 < noncentralChiSquaredQuantile n δ p := by
  apply (lt_lowerQuantile_iff (noncentralChiSquared n δ) p).2
  simpa [cdf_eq_real, measureReal_def, noncentralChiSquared_Iic_zero n δ hn] using p.2.1

/-- The empty-sum law has zero as all its interior quantiles. -/
@[simp] lemma noncentralChiSquaredQuantile_zero_dim (δ : ℝ≥0) (p : Ioo (0 : ℝ) 1) :
    noncentralChiSquaredQuantile 0 δ p = 0 := by
  simp [noncentralChiSquaredQuantile]

end ProbabilityTheory
