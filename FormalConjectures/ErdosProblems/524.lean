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
# Erdős Problem 524

*References:*
- [erdosproblems.com/524](https://www.erdosproblems.com/524)
- [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int.
  Közl. (1961), 221–254, p. 253.
- [SaZy54] Salem, R. and Zygmund, A., _Some properties of trigonometric series whose
  terms have random signs_. Acta Math. (1954), 245–301.
- [LS26] Letwin, Brayden and Sawhney, Mehtaab, _On the maxima of Littlewood polynomials
  on [-1,1]_. [arXiv:2604.19294](https://arxiv.org/abs/2604.19294), Theorems 1.1–1.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Erdos524

/-- Independent, measurable signs, each equal to $1$ or $-1$ with probability $1/2$. -/
structure IsRademacherSequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a : ℕ → Ω → ℝ) : Prop where
  indep : iIndepFun a μ
  measurable : ∀ k, Measurable (a k)
  prob_pos : ∀ k, μ {ω | a k ω = 1} = 1 / 2
  prob_neg : ∀ k, μ {ω | a k ω = -1} = 1 / 2

/-- The interval on which the random polynomial is maximized. -/
abbrev Interval := Set.Icc (-1 : ℝ) 1

instance : Nonempty Interval := ⟨⟨0, by norm_num⟩⟩

/-- The polynomial with coefficients indexed from $1$ through $n$. -/
noncomputable def randomPoly (a : ℕ → ℝ) (n : ℕ) : C(Interval, ℝ) :=
  ⟨fun x => ∑ k ∈ Finset.range n, a (k + 1) * (x : ℝ) ^ (k + 1),
    continuous_finsetSum _ fun _k _ => continuous_const.mul (continuous_subtype_val.pow _)⟩

/-- The paper's polynomial, which also includes the constant coefficient. -/
noncomputable def fullPoly (a : ℕ → ℝ) (n : ℕ) : C(Interval, ℝ) :=
  ContinuousMap.const Interval (a 0) + randomPoly a n

/-- The maximum absolute value on $[-1,1]$, with coefficients indexed from $1$. -/
noncomputable def supNorm (a : ℕ → ℝ) (n : ℕ) : ℝ := ‖randomPoly a n‖

/-- The maximum absolute value for the paper's indexing $0,\ldots,n$. -/
noncomputable def fullSupNorm (a : ℕ → ℝ) (n : ℕ) : ℝ := ‖fullPoly a n‖

@[simp, category API]
lemma norm_const_interval (c : ℝ) : ‖ContinuousMap.const Interval c‖ = |c| := by
  simp [ContinuousMap.norm_eq_iSup_norm]

@[simp, category API]
lemma randomPoly_zero (a : ℕ → ℝ) : randomPoly a 0 = 0 := by
  ext x
  simp [randomPoly]

@[simp, category API]
lemma supNorm_zero (a : ℕ → ℝ) : supNorm a 0 = 0 := by
  simp [supNorm]

@[simp, category API]
lemma fullSupNorm_zero (a : ℕ → ℝ) : fullSupNorm a 0 = |a 0| := by
  simp [fullSupNorm, fullPoly]

@[category API]
lemma supNorm_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ supNorm a n := norm_nonneg _

/-- Adding the constant coefficient changes the maximum by at most its absolute value. -/
@[category API]
lemma abs_fullSupNorm_sub_supNorm_le (a : ℕ → ℝ) (n : ℕ) :
    |fullSupNorm a n - supNorm a n| ≤ |a 0| := by
  have h := abs_norm_sub_norm_le (fullPoly a n) (randomPoly a n)
  simpa [fullSupNorm, supNorm, fullPoly] using h

/-- Evaluation at zero bounds the paper's maximum below by the constant coefficient. -/
@[category API]
lemma abs_constant_le_fullSupNorm (a : ℕ → ℝ) (n : ℕ) :
    |a 0| ≤ fullSupNorm a n := by
  have h := (fullPoly a n).norm_coe_le_norm ⟨0, by norm_num⟩
  simpa [fullPoly, randomPoly, fullSupNorm] using h

/-- A sign constant coefficient ensures that the paper's maximum is at least one. -/
@[category API]
lemma one_le_fullSupNorm (a : ℕ → ℝ) (n : ℕ) (h : |a 0| = 1) :
    1 ≤ fullSupNorm a n := by
  simpa [h] using abs_constant_le_fullSupNorm a n

/-- On $[-1,1]$, a polynomial with $n$ sign coefficients has maximum at most $n$. -/
@[category API]
lemma supNorm_le (a : ℕ → ℝ) (n : ℕ) (h : ∀ k, |a k| = 1) :
    supNorm a n ≤ n := by
  apply ((randomPoly a n).norm_le (Nat.cast_nonneg n)).mpr
  intro x
  change |∑ k ∈ Finset.range n, a (k + 1) * (x : ℝ) ^ (k + 1)| ≤ (n : ℝ)
  calc
    _ ≤ ∑ k ∈ Finset.range n, |a (k + 1) * (x : ℝ) ^ (k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul, h, one_mul, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr x.property)
    _ = n := by simp

/-- The sharp logarithmic normalization of the lower envelope. -/
noncomputable def normalizedLog (M : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (M n / Real.sqrt n) / (Real.log (Real.log n)) ^ (1 / 3 : ℝ)

/--
For any $t\in(0,1)$ let $t=\sum_{k=1}^{\infty}\epsilon_k(t)2^{-k}$, where
$\epsilon_k(t)\in\{0,1\}$. What is the correct order of magnitude, for almost all $t$, of
$M_n(t)=\max_{x\in[-1,1]}|\sum_{1\le k\le n}(-1)^{\epsilon_k(t)}x^k|$?

The binary digits give independent Rademacher signs under Lebesgue measure. In this model,
[LS26] determines the lower envelope's sharp logarithmic constant. Their polynomial includes
the constant coefficient; removing it changes the maximum by at most one.
-/
@[category research solved, AMS 26 60]
theorem erdos_524 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence μ a) :
    ∀ᵐ ω ∂μ, liminf (normalizedLog (supNorm (fun k => a k ω))) atTop =
      -((3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)) := by
  sorry

/-- The sharp lower-envelope constant in [LS26], with coefficients indexed $0,\ldots,n$. -/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.with_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℕ → Ω → ℝ)
    (ha : IsRademacherSequence μ a) :
    ∀ᵐ ω ∂μ, liminf (normalizedLog (fullSupNorm (fun k => a k ω))) atTop =
      -((3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)) := by
  sorry

/--
The Gaussian profile $\int_0^1 e^{-st}\,dB_s$, expressed by integration by parts against
the continuous Brownian path.
-/
noncomputable def gaussianProfile {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-t) * B 1 ω - B 0 ω +
    t * ∫ s in (0 : ℝ)..1, Real.exp (-s * t) * B (Real.toNNReal s) ω

/-- The small-ball distribution $F(\delta)$ of the supremum of the Gaussian profile. -/
noncomputable def smallBall {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (δ : ℝ) : ℝ :=
  (ν {ω | ∀ t : ℝ, 0 ≤ t → |gaussianProfile B t ω| ≤ δ}).toReal

/-- The inverse small-ball scale. Its argument is eventually in $(0,1)$ in the theorem below. -/
noncomputable def lowerScale {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n * Function.invFun (smallBall ν B) ((Real.log n) ^ (-1 / 2 : ℝ))

/--
Theorem 1.1 of [LS26] determines the full lower envelope via the inverse small-ball
distribution: almost surely, $\liminf M_n/(\sqrt n F^{-1}((\log n)^{-1/2}))=1$.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.inverse_small_ball
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence μ a)
    (B : ℝ≥0 → Ξ → ℝ) (hB : IsBrownianReal B ν) :
    ∀ᵐ ω ∂μ, liminf (fun n => fullSupNorm (fun k => a k ω) n / lowerScale ν B n)
      atTop = 1 := by
  sorry

end Erdos524
