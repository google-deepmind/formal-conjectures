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

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Bounded stochastic payoff evaluations

Cesàro, discounted, and long-run payoffs of a uniformly bounded measurable reward process.
The expectation of a pathwise lower limit and the lower limit of expectations are separate
definitions. Discounting uses the rate convention: patience means that the rate tends to zero.

The Cesàro--discounted identity is Abel summation. For its use in stochastic games, see
[Neyman, *Robust Optimization in Stochastic Games*, §3.6](https://arxiv.org/abs/2611.01151).
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology

namespace BoundedPayoffs

variable {Ω : Type*} [MeasurableSpace Ω]

theorem norm_liminf_le_of_bound {x : ℕ → ℝ} {B : ℝ} (hx : ∀ n, ‖x n‖ ≤ B) :
    ‖liminf x atTop‖ ≤ B := by
  have hle : ∀ n, x n ≤ B := fun n ↦ (abs_le.mp (hx n)).2
  have hge : ∀ n, -B ≤ x n := fun n ↦ (abs_le.mp (hx n)).1
  have hb : atTop.IsBoundedUnder (· ≥ ·) x :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hge)
  have ha : atTop.IsBoundedUnder (· ≤ ·) x :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hle)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_liminf_of_le ha.isCoboundedUnder_ge (Eventually.of_forall hge),
    liminf_le_limsup ha hb |>.trans (limsup_le_of_le hb.isCoboundedUnder_le
      (Eventually.of_forall hle))⟩

theorem norm_limsup_le_of_bound {x : ℕ → ℝ} {B : ℝ} (hx : ∀ n, ‖x n‖ ≤ B) :
    ‖limsup x atTop‖ ≤ B := by
  have hle : ∀ n, x n ≤ B := fun n ↦ (abs_le.mp (hx n)).2
  have hge : ∀ n, -B ≤ x n := fun n ↦ (abs_le.mp (hx n)).1
  have hb : atTop.IsBoundedUnder (· ≥ ·) x :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hge)
  have ha : atTop.IsBoundedUnder (· ≤ ·) x :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hle)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(le_liminf_of_le ha.isCoboundedUnder_ge (Eventually.of_forall hge)).trans
    (liminf_le_limsup ha hb), limsup_le_of_le hb.isCoboundedUnder_le
      (Eventually.of_forall hle)⟩

/-- A measurable real reward at each time, with a common deterministic bound. -/
structure Process (Ω : Type*) [MeasurableSpace Ω] where
  reward : ℕ → Ω → ℝ
  measurable_reward : ∀ t, Measurable (reward t)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_reward_le : ∀ t ω, ‖reward t ω‖ ≤ bound

namespace Process

variable (X : Process Ω)

/-- The average of the first `N` rewards. Time zero is the first stage. -/
noncomputable def average (N : ℕ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ t ∈ range N, X.reward t ω

@[simp] theorem average_zero (ω : Ω) : X.average 0 ω = 0 := by simp [average]

@[fun_prop] theorem measurable_average (N : ℕ) : Measurable (X.average N) := by
  exact measurable_const.mul (Finset.measurable_sum _ fun t _ ↦ X.measurable_reward t)

theorem norm_average_le (N : ℕ) (ω : Ω) : ‖X.average N ω‖ ≤ X.bound := by
  by_cases hN : N = 0
  · simpa [hN] using X.bound_nonneg
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  calc
    ‖X.average N ω‖ = (N : ℝ)⁻¹ * ‖∑ t ∈ range N, X.reward t ω‖ := by
      simp [average, norm_mul]
    _ ≤ (N : ℝ)⁻¹ * ∑ t ∈ range N, ‖X.reward t ω‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * (N * X.bound) := by
      gcongr
      calc
        ∑ t ∈ range N, ‖X.reward t ω‖ ≤ ∑ _t ∈ range N, X.bound :=
          Finset.sum_le_sum fun t _ ↦ X.norm_reward_le t ω
        _ = N * X.bound := by simp
    _ = X.bound := by field_simp

theorem integrable_reward (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) :
    Integrable (X.reward t) μ :=
  (integrable_const X.bound).mono' (X.measurable_reward t).aestronglyMeasurable
    (Eventually.of_forall (X.norm_reward_le t))

theorem integrable_average (μ : Measure Ω) [IsFiniteMeasure μ] (N : ℕ) :
    Integrable (X.average N) μ :=
  (integrable_const X.bound).mono' (X.measurable_average N).aestronglyMeasurable
    (Eventually.of_forall (X.norm_average_le N))

/-- Expected finite-horizon average. -/
noncomputable def expectedAverage (μ : Measure Ω) (N : ℕ) : ℝ :=
  ∫ ω, X.average N ω ∂μ

theorem norm_expectedAverage_le (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    ‖X.expectedAverage μ N‖ ≤ X.bound := by
  simpa [expectedAverage] using norm_integral_le_of_norm_le_const
    (μ := μ) (Eventually.of_forall (X.norm_average_le N))

theorem expectedAverage_eq (μ : Measure Ω) [IsFiniteMeasure μ] (N : ℕ) :
    X.expectedAverage μ N = (N : ℝ)⁻¹ * ∑ t ∈ range N, ∫ ω, X.reward t ω ∂μ := by
  change (∫ ω, (N : ℝ)⁻¹ * ∑ t ∈ range N, X.reward t ω ∂μ) = _
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ fun t _ ↦ X.integrable_reward μ t

/-- The lower limit of averages along one realized path. -/
noncomputable def pathLiminf (ω : Ω) : ℝ :=
  liminf (fun N ↦ X.average N ω) atTop

@[fun_prop] theorem measurable_pathLiminf : Measurable X.pathLiminf :=
  Measurable.liminf X.measurable_average

theorem norm_pathLiminf_le (ω : Ω) : ‖X.pathLiminf ω‖ ≤ X.bound := by
  exact norm_liminf_le_of_bound (fun N ↦ X.norm_average_le N ω)

theorem integrable_pathLiminf (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable X.pathLiminf μ :=
  (integrable_const X.bound).mono' X.measurable_pathLiminf.aestronglyMeasurable
    (Eventually.of_forall X.norm_pathLiminf_le)

/-- Expectation of the pathwise lower limit; this differs from `liminfExpected`. -/
noncomputable def expectedPathLiminf (μ : Measure Ω) : ℝ := ∫ ω, X.pathLiminf ω ∂μ

/-- Lower limit of expected finite averages. -/
noncomputable def liminfExpected (μ : Measure Ω) : ℝ := liminf (X.expectedAverage μ) atTop

/-- Upper limit of expected finite averages, including deviations whose averages do not converge. -/
noncomputable def limsupExpected (μ : Measure Ω) : ℝ := limsup (X.expectedAverage μ) atTop

/-- Convergence to an actual expected-average payoff, with no default for nonexistent limits. -/
def HasExpectedLimit (μ : Measure Ω) (v : ℝ) : Prop :=
  Tendsto (X.expectedAverage μ) atTop (𝓝 v)

theorem norm_liminfExpected_le (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ‖X.liminfExpected μ‖ ≤ X.bound :=
  norm_liminf_le_of_bound (X.norm_expectedAverage_le μ)

theorem norm_limsupExpected_le (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ‖X.limsupExpected μ‖ ≤ X.bound :=
  norm_limsup_le_of_bound (X.norm_expectedAverage_le μ)

theorem norm_expectedPathLiminf_le (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ‖X.expectedPathLiminf μ‖ ≤ X.bound := by
  simpa [expectedPathLiminf] using norm_integral_le_of_norm_le_const
    (μ := μ) (Eventually.of_forall X.norm_pathLiminf_le)

end Process

/-- Stage weight for a normalized discount rate. -/
def discountWeight (rate : ℝ) (t : ℕ) : ℝ := rate * (1 - rate) ^ t

/-- Abel weight on the positive horizon `n + 1`. -/
def abelWeight (rate : ℝ) (n : ℕ) : ℝ := (n + 1) * rate ^ 2 * (1 - rate) ^ n

theorem summable_geometric_mul_of_bound {x : ℕ → ℝ} {B q : ℝ}
    (hq : 0 ≤ q) (hq' : q < 1) (hx : ∀ n, ‖x n‖ ≤ B) :
    Summable (fun n ↦ q ^ n * x n) := by
  refine ((summable_geometric_of_lt_one hq hq').mul_right B).of_norm_bounded ?_
  intro n
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq n)]
  exact mul_le_mul_of_nonneg_left (hx n) (pow_nonneg hq n)

theorem hasSum_discountWeight {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    HasSum (discountWeight rate) 1 := by
  have h := (hasSum_geometric_of_lt_one (by linarith : 0 ≤ 1 - rate)
    (by linarith : 1 - rate < 1)).mul_left rate
  convert! h using 1
  simp [sub_sub_cancel, ne_of_gt hrate]

/-- Abel summation for a bounded real sequence; the horizon index on the right is positive. -/
theorem abel_identity {x : ℕ → ℝ} {B rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1)
    (hx : ∀ n, ‖x n‖ ≤ B) :
    (∑' t, discountWeight rate t * x t) =
      ∑' n, abelWeight rate n * ((n + 1 : ℝ)⁻¹ * ∑ t ∈ range (n + 1), x t) := by
  let q := 1 - rate
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq' : q < 1 := by dsimp [q]; linarith
  have hsum := summable_geometric_mul_of_bound hq hq' hx
  have hgeom := summable_geometric_of_lt_one hq hq'
  have hp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsum.norm hgeom.norm
  have hi (n : ℕ) :
      (∑ k ∈ range (n + 1), (q ^ k * x k) * q ^ (n - k)) =
        q ^ n * ∑ k ∈ range (n + 1), x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    calc
      (q ^ k * x k) * q ^ (n - k) = (q ^ k * q ^ (n - k)) * x k := by ring
      _ = q ^ n * x k := by rw [← pow_add, Nat.add_sub_of_le hkn]
  simp_rw [hi] at hp
  have hs : (∑' n, q ^ n * ∑ t ∈ range (n + 1), x t) =
      (∑' n, q ^ n * x n) * (1 - q)⁻¹ := by
    rw [← hp, tsum_geometric_of_lt_one hq hq']
  calc
    (∑' t, discountWeight rate t * x t) = rate * ∑' t, q ^ t * x t := by
      simp_rw [discountWeight, mul_assoc]
      exact tsum_mul_left
    _ = rate ^ 2 * ∑' n, q ^ n * ∑ t ∈ range (n + 1), x t := by
      rw [hs]
      dsimp [q]
      have hrate0 : rate ≠ 0 := ne_of_gt hrate
      field_simp [hrate0]
      ring
    _ = ∑' n, rate ^ 2 * (q ^ n * ∑ t ∈ range (n + 1), x t) := tsum_mul_left.symm
    _ = ∑' n, abelWeight rate n *
        ((n + 1 : ℝ)⁻¹ * ∑ t ∈ range (n + 1), x t) := by
      apply tsum_congr
      intro n
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      dsimp [abelWeight, q]
      field_simp

theorem abelWeight_nonneg {rate : ℝ} (_hrate : 0 ≤ rate) (hrate' : rate ≤ 1) (n : ℕ) :
    0 ≤ abelWeight rate n := by
  unfold abelWeight
  positivity

theorem hasSum_abelWeight {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    HasSum (abelWeight rate) 1 := by
  have hq : ‖1 - rate‖ < 1 := by rw [Real.norm_of_nonneg (by linarith)]; linarith
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hq).mul_left (rate ^ 2)
  convert! h using 1
  · ext n
    simp only [abelWeight, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    ring
  · simp [sub_sub_cancel, ne_of_gt hrate]

theorem summable_abel_mul_of_bound {rate B : ℝ} {x : ℕ → ℝ}
    (hrate : 0 < rate) (hrate' : rate < 1) (hx : ∀ n, ‖x n‖ ≤ B) :
    Summable (fun n ↦ abelWeight rate n * x n) := by
  refine ((hasSum_abelWeight hrate hrate').summable.mul_right B).of_norm_bounded ?_
  intro n
  rw [norm_mul, Real.norm_of_nonneg (abelWeight_nonneg hrate.le hrate'.le n)]
  exact mul_le_mul_of_nonneg_left (hx n) (abelWeight_nonneg hrate.le hrate'.le n)

/-- The contribution of a fixed finite set of horizons vanishes with the discount rate. -/
theorem tendsto_abel_prefix (K : ℕ) :
    Tendsto (fun rate : ℝ ↦ ∑ n ∈ range K, abelWeight rate n) (𝓝 0) (𝓝 0) := by
  have h : Continuous (fun rate : ℝ ↦ ∑ n ∈ range K, abelWeight rate n) := by
    unfold abelWeight
    fun_prop
  simpa [abelWeight] using h.tendsto 0

/-- A one-sided eventual bound on averages transfers to their Abel mixture, up to its prefix. -/
theorem abel_mixture_le {x : ℕ → ℝ} {B δ rate : ℝ} (K : ℕ)
    (hrate : 0 < rate) (hrate' : rate < 1) (hδ : 0 ≤ δ)
    (hx : ∀ n, ‖x n‖ ≤ B) (htail : ∀ n, K ≤ n → x n ≤ δ) :
    (∑' n, abelWeight rate n * x n) ≤
      δ + B * ∑ n ∈ range K, abelWeight rate n := by
  let c : ℕ → ℝ := fun n ↦ if n ∈ range K then B * abelWeight rate n else 0
  have hc0 : ∀ n ∉ range K, c n = 0 := by intro n hn; simp only [c, if_neg hn]
  have hc : Summable c := summable_of_ne_finset_zero hc0
  have hw := hasSum_abelWeight hrate hrate'
  have h : (∑' n, abelWeight rate n * x n) ≤
      ∑' n, (abelWeight rate n * δ + c n) := by
    apply Summable.tsum_le_tsum _ (summable_abel_mul_of_bound hrate hrate' hx)
      ((hw.summable.mul_right δ).add hc)
    intro n
    have hw0 := abelWeight_nonneg hrate.le hrate'.le n
    by_cases hn : n ∈ range K
    · simp only [c, if_pos hn]
      have hx' : x n ≤ B := (abs_le.mp (hx n)).2
      nlinarith
    · simp only [c, if_neg hn, add_zero]
      exact mul_le_mul_of_nonneg_left (htail n (by simpa using hn)) hw0
  calc
    (∑' n, abelWeight rate n * x n) ≤ ∑' n, (abelWeight rate n * δ + c n) := h
    _ = δ + B * ∑ n ∈ range K, abelWeight rate n := by
      rw [Summable.tsum_add (hw.summable.mul_right δ) hc, tsum_mul_right,
        hw.tsum_eq, one_mul, tsum_eq_sum hc0, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      simp only [c, if_pos hn]

/-- One rate threshold works for every bounded sequence with the same eventual upper bound. -/
theorem exists_abel_mixture_bound {B δ : ℝ} (hδ : 0 < δ) (K : ℕ) :
    ∃ rate₀ : ℝ, 0 < rate₀ ∧ rate₀ < 1 ∧
      ∀ rate : ℝ, 0 < rate → rate ≤ rate₀ →
      ∀ x : ℕ → ℝ, (∀ n, ‖x n‖ ≤ B) → (∀ n, K ≤ n → x n ≤ δ) →
        (∑' n, abelWeight rate n * x n) ≤ 2 * δ := by
  have ht : Tendsto (fun rate : ℝ ↦ B * ∑ n ∈ range K, abelWeight rate n)
      (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_abel_prefix K).const_mul B
  obtain ⟨r, hr, hbound⟩ := Metric.tendsto_nhds_nhds.mp ht δ hδ
  refine ⟨min (1 / 2) (r / 2), lt_min (by norm_num) (by positivity),
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
  intro rate hrate hrater x hx htail
  have hrater' : rate < r := by
    have := hrater.trans (min_le_right _ _)
    linarith
  have hsmall : B * ∑ n ∈ range K, abelWeight rate n < δ := by
    have := hbound (x := rate) (by simpa [Real.dist_eq, abs_of_pos hrate] using hrater')
    exact (abs_lt.mp (by simpa [Real.dist_eq] using this)).2
  have hrate' : rate < 1 := lt_of_le_of_lt (hrater.trans (min_le_left _ _)) (by norm_num)
  exact (abel_mixture_le K hrate hrate' hδ.le hx htail).trans (by linarith)

/-- The same rate threshold transfers two-sided bounds for every bounded sequence. -/
theorem exists_abel_mixture_norm_bound {B δ : ℝ} (hδ : 0 < δ) (K : ℕ) :
    ∃ rate₀ : ℝ, 0 < rate₀ ∧ rate₀ < 1 ∧
      ∀ rate : ℝ, 0 < rate → rate ≤ rate₀ →
      ∀ x : ℕ → ℝ, (∀ n, ‖x n‖ ≤ B) → (∀ n, K ≤ n → ‖x n‖ ≤ δ) →
        ‖∑' n, abelWeight rate n * x n‖ ≤ 2 * δ := by
  obtain ⟨rate₀, hpos, hlt, hbound⟩ := exists_abel_mixture_bound (B := B) hδ K
  refine ⟨rate₀, hpos, hlt, ?_⟩
  intro rate hrate hrater x hx htail
  have hupper := hbound rate hrate hrater x hx
    (fun n hn ↦ (abs_le.mp (htail n hn)).2)
  have hlower := hbound rate hrate hrater (fun n ↦ -x n)
    (by simpa using hx) (fun n hn ↦ by have := (abs_le.mp (htail n hn)).1; linarith)
  simp only [mul_neg, tsum_neg] at hlower
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hupper⟩

namespace Process

variable (X : Process Ω)

/-- Normalized discounted payoff along a realized path. The rate must lie in `(0,1)` in uses. -/
noncomputable def discounted (rate : ℝ) (ω : Ω) : ℝ :=
  ∑' t, discountWeight rate t * X.reward t ω

/-- Expected normalized discounted payoff. -/
noncomputable def expectedDiscounted (μ : Measure Ω) (rate : ℝ) : ℝ :=
  ∫ ω, X.discounted rate ω ∂μ

theorem summable_discounted {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) (ω : Ω) :
    Summable (fun t ↦ discountWeight rate t * X.reward t ω) := by
  simpa only [discountWeight, mul_assoc] using
    (summable_geometric_mul_of_bound (by linarith : 0 ≤ 1 - rate)
      (by linarith : 1 - rate < 1) (fun n ↦ X.norm_reward_le n ω)).mul_left rate

@[fun_prop] theorem measurable_discounted (rate : ℝ) : Measurable (X.discounted rate) := by
  exact Measurable.tsum fun t ↦ measurable_const.mul (X.measurable_reward t)

theorem norm_discounted_le {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) (ω : Ω) :
    ‖X.discounted rate ω‖ ≤ X.bound := by
  have hw := hasSum_discountWeight hrate hrate'
  calc
    ‖X.discounted rate ω‖ ≤ ∑' t, ‖discountWeight rate t * X.reward t ω‖ :=
      norm_tsum_le_tsum_norm (X.summable_discounted hrate hrate' ω).norm
    _ ≤ ∑' t, discountWeight rate t * X.bound := by
      apply Summable.tsum_le_tsum _ (X.summable_discounted hrate hrate' ω).norm
        (hw.summable.mul_right X.bound)
      intro t
      change ‖rate * (1 - rate) ^ t * X.reward t ω‖ ≤
        rate * (1 - rate) ^ t * X.bound
      rw [norm_mul, Real.norm_of_nonneg
        (mul_nonneg hrate.le (pow_nonneg (by linarith : 0 ≤ 1 - rate) t))]
      exact mul_le_mul_of_nonneg_left (X.norm_reward_le t ω)
        (mul_nonneg hrate.le (pow_nonneg (by linarith : 0 ≤ 1 - rate) t))
    _ = X.bound := by rw [tsum_mul_right, hw.tsum_eq, one_mul]

theorem integrable_discounted (μ : Measure Ω) [IsFiniteMeasure μ]
    {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) : Integrable (X.discounted rate) μ :=
  (integrable_const X.bound).mono' (X.measurable_discounted rate).aestronglyMeasurable
    (Eventually.of_forall (X.norm_discounted_le hrate hrate'))

theorem norm_expectedDiscounted_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    ‖X.expectedDiscounted μ rate‖ ≤ X.bound := by
  simpa [expectedDiscounted] using norm_integral_le_of_norm_le_const
    (μ := μ) (Eventually.of_forall (X.norm_discounted_le hrate hrate'))

theorem expectedDiscounted_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    X.expectedDiscounted μ rate = ∑' t, discountWeight rate t * ∫ ω, X.reward t ω ∂μ := by
  have hw := hasSum_discountWeight hrate hrate'
  have hnorm (t : ℕ) :
      ‖∫ ω, ‖discountWeight rate t * X.reward t ω‖ ∂μ‖ ≤
        discountWeight rate t * X.bound := by
    have hw0 : 0 ≤ discountWeight rate t :=
      mul_nonneg hrate.le (pow_nonneg (by linarith : 0 ≤ 1 - rate) t)
    have hbound (ω : Ω) : ‖‖discountWeight rate t * X.reward t ω‖‖ ≤
        discountWeight rate t * X.bound := by
      rw [norm_norm, norm_mul, Real.norm_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left (X.norm_reward_le t ω) hw0
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall hbound)
  have hs : Summable (fun t ↦ ∫ ω, ‖discountWeight rate t * X.reward t ω‖ ∂μ) :=
    (hw.summable.mul_right X.bound).of_norm_bounded hnorm
  change (∫ ω, ∑' t, discountWeight rate t * X.reward t ω ∂μ) = _
  rw [← integral_tsum_of_summable_integral_norm
      (fun t ↦ (X.integrable_reward μ t).const_mul _) hs]
  apply tsum_congr
  intro t
  exact integral_const_mul _ _

/-- Expected discounted payoffs are Abel mixtures of expected positive-horizon averages. -/
theorem expected_abel_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    X.expectedDiscounted μ rate =
      ∑' n, abelWeight rate n * X.expectedAverage μ (n + 1) := by
  rw [X.expectedDiscounted_eq μ hrate hrate']
  have hx (t : ℕ) : ‖∫ ω, X.reward t ω ∂μ‖ ≤ X.bound := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := μ) (Eventually.of_forall (X.norm_reward_le t))
  rw [abel_identity hrate hrate' hx]
  apply tsum_congr
  intro n
  rw [X.expectedAverage_eq]
  simp

/-- Every actual expected-average limit remains within the stage-reward bound. -/
theorem norm_of_HasExpectedLimit (μ : Measure Ω) [IsProbabilityMeasure μ] {v : ℝ}
    (hv : X.HasExpectedLimit μ v) : ‖v‖ ≤ X.bound :=
  le_of_tendsto hv.norm (Eventually.of_forall (X.norm_expectedAverage_le μ))

/-- Constant reward process, useful for checking payoff normalizations. -/
def const (c : ℝ) : Process Ω where
  reward := fun _ _ ↦ c
  measurable_reward := fun _ ↦ measurable_const
  bound := ‖c‖
  bound_nonneg := norm_nonneg _
  norm_reward_le := fun _ _ ↦ le_rfl

@[simp] theorem average_constant (c : ℝ) (N : ℕ) (hN : N ≠ 0) (ω : Ω) :
    (const c).average N ω = c := by
  simp [average, const, Nat.cast_ne_zero.mpr hN]

@[simp] theorem discounted_constant (c : ℝ) {rate : ℝ}
    (hrate : 0 < rate) (hrate' : rate < 1) (ω : Ω) :
    (const c).discounted rate ω = c := by
  change (∑' t, discountWeight rate t * c) = c
  rw [tsum_mul_right, (hasSum_discountWeight hrate hrate').tsum_eq, one_mul]

@[simp] theorem pathLiminf_constant (c : ℝ) (ω : Ω) : (const c).pathLiminf ω = c := by
  have he : (fun N ↦ (const c).average N ω) =ᶠ[atTop] (fun _ ↦ c) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact average_constant c N (ne_of_gt hN) ω
  rw [pathLiminf, liminf_congr he, liminf_const]

@[simp] theorem expectedPathLiminf_constant (c : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : (const c).expectedPathLiminf μ = c := by
  simp [expectedPathLiminf]

@[simp] theorem expectedDiscounted_constant (c : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    (const c).expectedDiscounted μ rate = c := by
  simp [expectedDiscounted, discounted_constant c hrate hrate']

end Process

end BoundedPayoffs
