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

public import FormalConjecturesForMathlib.Probability.Distributions.NoncentralChiSquared
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact asymptotic relative bias in a one-regressor IV model

For $k>2$, the relative bias is represented by
$\int_0^1 \exp[-\delta(1-u^{2/(k-2)})/2]\,du$.
For $k=2$, it is $\exp(-\delta/2)$.

Skeels and Windmeijer's Theorem 1 identifies the Gaussian-ratio expectation with
${}_1F_1(1;k/2;-\delta/2)$. Euler's integral formula gives
$(k/2-1)\int_0^1 e^{-\delta t/2}(1-t)^{k/2-2}\,dt$ for $k>2$.
The substitution $u=(1-t)^{k/2-1}$ gives the representation used here.
The factor $k/2-1$ uses the ordinary Kummer function, rather than the regularized one.

## References

* C. L. Skeels and F. Windmeijer, [*On the Stock–Yogo Tables*]
  (https://doi.org/10.3390/econometrics6040044), Theorem 1, equations (9)–(10).
* [DLMF 13.4.1](https://dlmf.nist.gov/13.4.E1) and
  [DLMF 13.2.4](https://dlmf.nist.gov/13.2.E4), Euler's integral and its normalization.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace InstrumentalVariables

/-- Instrument counts for which the source's relative bias exists. -/
abbrev InstrumentCount := {k : ℕ // 2 ≤ k}

/-- The exponent coefficient on the unit interval in the compact relative-bias integral. -/
noncomputable def biasRate (k : InstrumentCount) (u : ℝ) : ℝ :=
  if k.val = 2 then 1 else 1 - u ^ (2 / ((k.val : ℝ) - 2))

private lemma biasExponent_pos (k : InstrumentCount) (hk : k.val ≠ 2) :
    0 < 2 / ((k.val : ℝ) - 2) := by
  have : 2 < k.val := lt_of_le_of_ne k.property (Ne.symm hk)
  have : (2 : ℝ) < k.val := by exact_mod_cast this
  positivity

@[simp] lemma biasRate_zero (k : InstrumentCount) : biasRate k 0 = 1 := by
  unfold biasRate
  split_ifs with hk
  · rfl
  · rw [Real.zero_rpow (biasExponent_pos k hk).ne']
    norm_num

@[simp] lemma biasRate_one (k : InstrumentCount) :
    biasRate k 1 = if k.val = 2 then 1 else 0 := by
  simp [biasRate]

lemma continuous_biasRate (k : InstrumentCount) : Continuous (biasRate k) := by
  unfold biasRate
  split_ifs with hk
  · exact continuous_const
  · exact continuous_const.sub (Real.continuous_rpow_const (biasExponent_pos k hk).le)

lemma biasRate_mem_Icc (k : InstrumentCount) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    biasRate k u ∈ Icc (0 : ℝ) 1 := by
  unfold biasRate
  split_ifs with hk
  · norm_num
  · have hp := biasExponent_pos k hk
    have h0 := Real.rpow_nonneg hu.1 (2 / ((k.val : ℝ) - 2))
    have h1 := Real.rpow_le_one hu.1 hu.2 hp.le
    constructor <;> linarith

lemma biasRate_pos (k : InstrumentCount) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    0 < biasRate k u := by
  unfold biasRate
  split_ifs with hk
  · norm_num
  · exact sub_pos.2 (Real.rpow_lt_one hu.1 hu.2 (biasExponent_pos k hk))

/-- The exact source bias, in its nonsingular compact-integral representation. -/
noncomputable def relativeBias (k : InstrumentCount) (δ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, Real.exp (-δ / 2 * biasRate k u)

lemma continuous_relativeBias_integrand (k : InstrumentCount) (δ : ℝ) :
    Continuous (fun u ↦ Real.exp (-δ / 2 * biasRate k u)) := by
  exact (continuous_const.mul (continuous_biasRate k)).rexp

lemma intervalIntegrable_relativeBias (k : InstrumentCount) (δ : ℝ) :
    IntervalIntegrable (fun u ↦ Real.exp (-δ / 2 * biasRate k u)) volume 0 1 :=
  (continuous_relativeBias_integrand k δ).intervalIntegrable _ _

lemma continuous_relativeBias (k : InstrumentCount) : Continuous (relativeBias k) := by
  change Continuous (fun δ : ℝ ↦ ∫ u in (0 : ℝ)..1, Real.exp (-δ / 2 * biasRate k u))
  have h : Continuous (fun δ : ℝ ↦ ∫ u in Icc (0 : ℝ) 1,
      Real.exp (-δ / 2 * biasRate k u)) :=
    continuous_parametric_integral_of_continuous
      (((continuous_fst.neg.div_const 2).mul
        ((continuous_biasRate k).comp continuous_snd)).rexp) isCompact_Icc
  simpa only [relativeBias, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

@[simp] lemma relativeBias_zero (k : InstrumentCount) : relativeBias k 0 = 1 := by
  simp [relativeBias]

lemma strictAnti_relativeBias (k : InstrumentCount) : StrictAnti (relativeBias k) := by
  intro δ ε hδε
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1)
    (continuous_relativeBias_integrand k ε).continuousOn
    (continuous_relativeBias_integrand k δ).continuousOn
  · intro u hu
    apply Real.exp_le_exp.2
    have hr := (biasRate_mem_Icc k ⟨hu.1.le, hu.2⟩).1
    nlinarith
  · refine ⟨0, by norm_num, Real.exp_lt_exp.2 ?_⟩
    have hr := biasRate_pos k (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
    nlinarith

lemma relativeBias_pos (k : InstrumentCount) (δ : ℝ) : 0 < relativeBias k δ := by
  exact intervalIntegral.intervalIntegral_pos_of_pos (intervalIntegrable_relativeBias k δ)
    (fun _ ↦ Real.exp_pos _) (by norm_num)

/-- Positive concentration gives an interior relative bias. -/
lemma relativeBias_mem_Ioo (k : InstrumentCount) {δ : ℝ} (hδ : 0 < δ) :
    relativeBias k δ ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨relativeBias_pos k δ, ?_⟩
  simpa using strictAnti_relativeBias k hδ

lemma tendsto_relativeBias_atTop (k : InstrumentCount) :
    Tendsto (relativeBias k) atTop (𝓝 0) := by
  change Tendsto (fun δ : ℝ ↦ ∫ u in (0 : ℝ)..1, Real.exp (-δ / 2 * biasRate k u)) atTop (𝓝 0)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun δ u ↦ Real.exp (-δ / 2 * biasRate k u)) (f := fun _ ↦ (0 : ℝ))
    (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun δ ↦
      (continuous_relativeBias_integrand k δ).aestronglyMeasurable.restrict)
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with δ hδ
      filter_upwards with u hu
      have hu' : 0 < u ∧ u ≤ 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioc] using hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      have := (biasRate_mem_Icc k ⟨hu'.1.le, hu'.2⟩).1
      nlinarith)
    intervalIntegrable_const
    (by
      filter_upwards [volume.ae_ne (1 : ℝ)] with u hu huI
      have huI' : 0 < u ∧ u ≤ 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioc] using huI
      have hr := biasRate_pos k ⟨huI'.1.le, lt_of_le_of_ne huI'.2 hu⟩
      have ht : Tendsto (fun δ : ℝ ↦ -δ / 2 * biasRate k u) atTop atBot := by
        convert tendsto_id.atTop_mul_const_of_neg
          (show -biasRate k u / 2 < 0 by linarith) using 1
        ext δ
        dsimp only [id_eq]
        ring
      exact Real.tendsto_exp_atBot.comp ht)
  simpa only [relativeBias, intervalIntegral.integral_zero] using h

/-- Every interior tolerated bias has exactly one nonnegative concentration parameter. -/
lemma existsUnique_concentrationParameter (k : InstrumentCount) (B : Ioo (0 : ℝ) 1) :
    ∃! δ : ℝ, 0 ≤ δ ∧ relativeBias k δ = B.1 := by
  obtain ⟨d, hd, hd0⟩ := (((tendsto_relativeBias_atTop k).eventually_lt_const B.2.1).and
    (eventually_ge_atTop (0 : ℝ))).exists
  have hbd : relativeBias k d ≤ B.1 := hd.le
  have hb0 : B.1 ≤ relativeBias k 0 := by simpa using B.2.2.le
  obtain ⟨δ, hδ, hval⟩ := intermediate_value_Icc' hd0
    (continuous_relativeBias k).continuousOn ⟨hbd, hb0⟩
  refine ⟨δ, ⟨hδ.1, hval⟩, ?_⟩
  intro ε hε
  exact (strictAnti_relativeBias k).injective (hε.2.trans hval.symm)

/-- The unique concentration parameter that gives the specified interior relative bias. -/
noncomputable def concentrationParameter (k : InstrumentCount) (B : Ioo (0 : ℝ) 1) : ℝ≥0 :=
  ⟨Classical.choose (existsUnique_concentrationParameter k B),
    (Classical.choose_spec (existsUnique_concentrationParameter k B)).1.1⟩

lemma relativeBias_concentrationParameter (k : InstrumentCount) (B : Ioo (0 : ℝ) 1) :
    relativeBias k (concentrationParameter k B) = B.1 :=
  (Classical.choose_spec (existsUnique_concentrationParameter k B)).1.2

lemma concentrationParameter_pos (k : InstrumentCount) (B : Ioo (0 : ℝ) 1) :
    0 < concentrationParameter k B := by
  apply pos_iff_ne_zero.2
  intro h
  have hb := relativeBias_concentrationParameter k B
  have hcoe : (concentrationParameter k B : ℝ) = 0 := by exact_mod_cast h
  rw [hcoe, relativeBias_zero] at hb
  exact B.2.2.ne hb.symm

lemma concentrationParameter_unique (k : InstrumentCount) (B : Ioo (0 : ℝ) 1)
    {δ : ℝ≥0} (hδ : relativeBias k δ = B.1) : δ = concentrationParameter k B := by
  apply NNReal.coe_injective
  exact (strictAnti_relativeBias k).injective
    (hδ.trans (relativeBias_concentrationParameter k B).symm)

@[simp] lemma relativeBias_two (δ : ℝ) :
    relativeBias ⟨2, le_rfl⟩ δ = Real.exp (-δ / 2) := by
  simp [relativeBias, biasRate]

lemma concentrationParameter_two (B : Ioo (0 : ℝ) 1) :
    (concentrationParameter ⟨2, le_rfl⟩ B : ℝ) = -2 * Real.log B.1 := by
  have h := relativeBias_concentrationParameter ⟨2, le_rfl⟩ B
  rw [relativeBias_two] at h
  have hh := congrArg Real.log h
  rw [Real.log_exp] at hh
  linarith

/-- The exact normalized noncentral chi-squared critical value at an interior probability. -/
noncomputable def weakInstrumentCriticalValue (k : InstrumentCount) (B : Ioo (0 : ℝ) 1)
    (p : Ioo (0 : ℝ) 1) : ℝ :=
  ProbabilityTheory.noncentralChiSquaredQuantile k.val (concentrationParameter k B) p / k.val

lemma weakInstrumentCriticalValue_pos (k : InstrumentCount) (B p : Ioo (0 : ℝ) 1) :
    0 < weakInstrumentCriticalValue k B p := by
  apply div_pos (ProbabilityTheory.noncentralChiSquaredQuantile_pos _ _ _ (by omega))
  exact_mod_cast (show 0 < k.val by omega)

/-- Rescaling the critical value gives exactly the specified cumulative probability. -/
lemma cdf_weakInstrumentCriticalValue (k : InstrumentCount) (B p : Ioo (0 : ℝ) 1) :
    ProbabilityTheory.cdf
      (ProbabilityTheory.noncentralChiSquared k.val (concentrationParameter k B))
      ((k.val : ℝ) * weakInstrumentCriticalValue k B p) = p.1 := by
  have hk : (k.val : ℝ) ≠ 0 := by exact_mod_cast (show k.val ≠ 0 by omega)
  have hmul : (k.val : ℝ) * weakInstrumentCriticalValue k B p =
      ProbabilityTheory.noncentralChiSquaredQuantile k.val (concentrationParameter k B) p := by
    unfold weakInstrumentCriticalValue
    field_simp
  rw [hmul]
  exact ProbabilityTheory.cdf_noncentralChiSquaredQuantile _ _ _ (by omega)

end InstrumentalVariables
