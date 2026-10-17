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

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic

/-!
# Uniform distribution relative to a subdivision

Half-open interval interpolation, almost-everywhere distribution for positive
parameters, invariance under finite changes, and sufficient conditions on
subdivision boundaries.

*References:*
- [Davenport–Erdős (1963), pp. 3–4](https://www.renyi.hu/~p_erdos/1963-01.pdf)
- [Erdős (1975), §5](https://www.renyi.hu/~p_erdos/1975-31.pdf)
-/

@[expose] public section

namespace SubdivisionDistribution

/-- The index of a half-open gap containing `x`. -/
def InGap (a : ℕ → ℕ) (x : ℝ) (i : ℕ) : Prop :=
  (a i : ℝ) ≤ x ∧ x < (a (i + 1) : ℝ)

theorem exists_inGap {a : ℕ → ℕ} (ha : StrictMono a) {x : ℝ}
    (hx : (a 0 : ℝ) ≤ x) : ∃ i, InGap a x i := by
  have hu : ∃ j, x < (a j : ℝ) := by
    obtain ⟨j, hj⟩ := exists_nat_gt x
    exact ⟨j, hj.trans_le (by exact_mod_cast ha.le_apply (x := j))⟩
  have hj : x < (a (Nat.find hu) : ℝ) := Nat.find_spec hu
  have hj0 : Nat.find hu ≠ 0 := by
    intro h
    rw [h] at hj
    exact (not_lt_of_ge hx) hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨i, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hu (by omega : i < Nat.find hu))
  · simpa [hi] using hj

theorem inGap_unique {a : ℕ → ℕ} (ha : StrictMono a) {x : ℝ} {i j : ℕ}
    (hi : InGap a x i) (hj : InGap a x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hm : (a (i + 1) : ℝ) ≤ a j := by exact_mod_cast ha.monotone h
    exact False.elim (not_lt_of_ge (hm.trans hj.1) hi.2)
  · exact h
  · have hm : (a (j + 1) : ℝ) ≤ a i := by exact_mod_cast ha.monotone h
    exact False.elim (not_lt_of_ge (hm.trans hi.1) hj.2)

/-- Canonical interpolation, with harmless value zero below the first term. -/
noncomputable def gapFraction (a : ℕ → ℕ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ i, InGap a x i then
    (x - a (Classical.choose h)) /
      ((a (Classical.choose h + 1) : ℝ) - a (Classical.choose h))
  else 0

theorem gapFraction_eq {a : ℕ → ℕ} (ha : StrictMono a) {x : ℝ} {i : ℕ}
    (hi : InGap a x i) :
    gapFraction a x = (x - a i) / ((a (i + 1) : ℝ) - a i) := by
  have he : ∃ j, InGap a x j := ⟨i, hi⟩
  rw [gapFraction, dif_pos he]
  rw [inGap_unique ha (Classical.choose_spec he) hi]

theorem gapFraction_mem_Ico {a : ℕ → ℕ} (ha : StrictMono a) (x : ℝ) :
    gapFraction a x ∈ Set.Ico (0 : ℝ) 1 := by
  by_cases he : ∃ i, InGap a x i
  · obtain ⟨i, hi⟩ := he
    rw [gapFraction_eq ha hi]
    have hd : 0 < (a (i + 1) : ℝ) - a i := by
      have ht : (a i : ℝ) < a (i + 1) := by exact_mod_cast ha (Nat.lt_succ_self i)
      linarith
    refine ⟨div_nonneg (sub_nonneg.mpr hi.1) hd.le, ?_⟩
    apply (div_lt_one hd).mpr
    linarith [hi.2]
  · simp [gapFraction, he]

theorem gapFraction_eq_zero_of_lt {a : ℕ → ℕ} (ha : StrictMono a) {x : ℝ}
    (hx : x < (a 0 : ℝ)) : gapFraction a x = 0 := by
  have he : ¬ ∃ i, InGap a x i := by
    rintro ⟨i, hi⟩
    have hm : (a 0 : ℝ) ≤ a i := by exact_mod_cast ha.monotone (Nat.zero_le i)
    exact (not_lt_of_ge (hm.trans hi.1)) hx
  simp [gapFraction, he]

namespace RealSubdivision

/-- The index of a half-open gap containing `x`. -/
def InGap (a : ℕ → ℝ) (x : ℝ) (i : ℕ) : Prop :=
  (a i : ℝ) ≤ x ∧ x < (a (i + 1) : ℝ)

theorem exists_inGap {a : ℕ → ℝ} (_ha : StrictMono a)
    (hu : Filter.Tendsto a Filter.atTop Filter.atTop) {x : ℝ}
    (hx : a 0 ≤ x) : ∃ i, InGap a x i := by
  have he : ∃ j, x < a j := (hu.eventually_gt_atTop x).exists
  have hj : x < a (Nat.find he) := Nat.find_spec he
  have hj0 : Nat.find he ≠ 0 := by
    intro h
    rw [h] at hj
    exact (not_lt_of_ge hx) hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨i, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min he (by omega : i < Nat.find he))
  · simpa [hi] using hj

theorem inGap_unique {a : ℕ → ℝ} (ha : StrictMono a) {x : ℝ} {i j : ℕ}
    (hi : InGap a x i) (hj : InGap a x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hm : (a (i + 1) : ℝ) ≤ a j := ha.monotone h
    exact False.elim (not_lt_of_ge (hm.trans hj.1) hi.2)
  · exact h
  · have hm : (a (j + 1) : ℝ) ≤ a i := ha.monotone h
    exact False.elim (not_lt_of_ge (hm.trans hi.1) hj.2)

/-- Canonical interpolation, with harmless value zero below the first term. -/
noncomputable def gapFraction (a : ℕ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ i, InGap a x i then
    (x - a (Classical.choose h)) /
      ((a (Classical.choose h + 1) : ℝ) - a (Classical.choose h))
  else 0

theorem gapFraction_eq {a : ℕ → ℝ} (ha : StrictMono a) {x : ℝ} {i : ℕ}
    (hi : InGap a x i) :
    gapFraction a x = (x - a i) / ((a (i + 1) : ℝ) - a i) := by
  have he : ∃ j, InGap a x j := ⟨i, hi⟩
  rw [gapFraction, dif_pos he]
  rw [inGap_unique ha (Classical.choose_spec he) hi]

theorem gapFraction_mem_Ico {a : ℕ → ℝ} (ha : StrictMono a) (x : ℝ) :
    gapFraction a x ∈ Set.Ico (0 : ℝ) 1 := by
  by_cases he : ∃ i, InGap a x i
  · obtain ⟨i, hi⟩ := he
    rw [gapFraction_eq ha hi]
    have hd : 0 < (a (i + 1) : ℝ) - a i := by
      have ht : (a i : ℝ) < a (i + 1) := ha (Nat.lt_succ_self i)
      linarith
    refine ⟨div_nonneg (sub_nonneg.mpr hi.1) hd.le, ?_⟩
    apply (div_lt_one hd).mpr
    linarith [hi.2]
  · simp [gapFraction, he]

theorem gapFraction_eq_zero_of_lt {a : ℕ → ℝ} (ha : StrictMono a) {x : ℝ}
    (hx : x < (a 0 : ℝ)) : gapFraction a x = 0 := by
  have he : ¬ ∃ i, InGap a x i := by
    rintro ⟨i, hi⟩
    have hm : (a 0 : ℝ) ≤ a i := ha.monotone (Nat.zero_le i)
    exact (not_lt_of_ge (hm.trans hi.1)) hx
  simp [gapFraction, he]

end RealSubdivision

end SubdivisionDistribution

namespace SubdivisionDistribution
open Filter MeasureTheory
open scoped Topology BigOperators

/-- Counts indices 0,...,N-1 in a half-open test interval. -/
noncomputable def intervalCount (s : ℕ → ℝ) (u v : ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => s n ∈ Set.Ico u v).card

/-- Real indicator used to express the counting average as a finite sum. -/
noncomputable def intervalIndicator (s : ℕ → ℝ) (u v : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if s n ∈ Set.Ico u v then 1 else 0

noncomputable def intervalFrequency (s : ℕ → ℝ) (u v : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, intervalIndicator s u v n

theorem intervalFrequency_eq_count (s : ℕ → ℝ) (u v : ℝ) (N : ℕ) :
    intervalFrequency s u v N = (intervalCount s u v N : ℝ) / N := by
  classical
  simp only [intervalFrequency, intervalIndicator, intervalCount, Finset.sum_boole]
  ring

/-- Standard interval-frequency definition of uniform distribution on [0,1).
It is invariant under arbitrary changes of finitely many entries. -/
def UniformlyDistributed (s : ℕ → ℝ) : Prop :=
  ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
    Tendsto (intervalFrequency s u v) atTop (𝓝 (v - u))

theorem intervalFrequency_sub_tendsto_zero {s t : ℕ → ℝ}
    (hst : s =ᶠ[atTop] t) (u v : ℝ) :
    Tendsto (fun N => intervalFrequency s u v N - intervalFrequency t u v N)
      atTop (𝓝 0) := by
  have hi : (fun n => intervalIndicator s u v n - intervalIndicator t u v n)
      =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hst] with n hn
    simp [intervalIndicator, hn]
  have hz := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hc := (hz.congr' hi.symm).cesaro
  simpa only [intervalFrequency, Finset.sum_sub_distrib, mul_sub] using hc

theorem uniformlyDistributed_congr {s t : ℕ → ℝ} (hst : s =ᶠ[atTop] t) :
    UniformlyDistributed s ↔ UniformlyDistributed t := by
  have transfer : ∀ {s t : ℕ → ℝ}, s =ᶠ[atTop] t →
      UniformlyDistributed t → UniformlyDistributed s := by
    intro s t he ht u v hu huv hv
    have h := (ht u v hu huv hv).add (intervalFrequency_sub_tendsto_zero he u v)
    simpa only [add_zero, add_sub_cancel] using h
  exact ⟨transfer hst.symm, transfer hst⟩

/-- A positive sampling parameter reaches the first boundary eventually. -/
theorem sample_eventually_above (α b : ℝ) (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, b ≤ α * (n + 1 : ℕ) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hm := hn.const_mul_atTop hα
  simpa only [Nat.cast_add, Nat.cast_one] using (hm.eventually (eventually_ge_atTop b))

/-- Almost everywhere on the positive half-line, with Lebesgue measure. -/
def AlmostAllPositive (P : ℝ → Prop) : Prop :=
  ∀ᵐ α ∂(volume.restrict (Set.Ioi (0 : ℝ))), P α

theorem almostAllPositive_iff (P : ℝ → Prop) :
    AlmostAllPositive P ↔ ∀ᵐ α ∂volume, 0 < α → P α := by
  exact ae_restrict_iff' measurableSet_Ioi

/-- Failure requires a positive-measure exceptional set, not just one α. -/
theorem not_almostAllPositive_iff (P : ℝ → Prop) :
    ¬ AlmostAllPositive P ↔ volume {α : ℝ | 0 < α ∧ ¬ P α} ≠ 0 := by
  rw [almostAllPositive_iff, ae_iff]
  simp only [Classical.not_imp]

/-- Successive ratios are real ratios. a(0)=0 is allowed; one initial
zero denominator cannot affect this limit. -/
def RatioTendsToOne (a : ℕ → ℕ) : Prop :=
  Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (𝓝 1)

/-- Zero-based index n samples the positive integer n+1. -/
noncomputable def sampled (a : ℕ → ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  gapFraction a (α * (n + 1 : ℕ))

/-- Almost-everywhere distribution assertion for natural subdivision boundaries. -/
def NatQuestion : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → RatioTendsToOne a →
    AlmostAllPositive (fun α => UniformlyDistributed (sampled a α))

/-- Literal negative answer, recorded as a proposition, not a proved result. -/
def NatCounterexampleStatement : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ RatioTendsToOne a ∧
    volume {α : ℝ | 0 < α ∧ ¬ UniformlyDistributed (sampled a α)} ≠ 0

theorem natCounterexample_iff_not_question : NatCounterexampleStatement ↔ ¬ NatQuestion := by
  classical
  simp only [NatCounterexampleStatement, NatQuestion, not_forall]
  simp_rw [not_almostAllPositive_iff]
  simp only [exists_prop]

/-- Any extension of the source formula below a(0) gives the same distribution
question; its choice cannot be used as an alleged counterexample. -/
theorem sampling_extension_invariant {a : ℕ → ℕ}
    {g : ℝ → ℝ} (hg : ∀ x, (a 0 : ℝ) ≤ x → g x = gapFraction a x)
    {α : ℝ} (hα : 0 < α) :
    UniformlyDistributed (fun n => g (α * (n + 1 : ℕ))) ↔
      UniformlyDistributed (sampled a α) := by
  apply uniformlyDistributed_congr
  filter_upwards [sample_eventually_above α (a 0) hα] with n hn
  exact hg _ hn

end SubdivisionDistribution

namespace SubdivisionDistribution
theorem natural_real_strictMono {a : ℕ → ℕ} (ha : StrictMono a) :
    StrictMono (fun i => (a i : ℝ)) := by
  intro i j hij
  change (a i : ℝ) < a j
  exact_mod_cast ha hij

theorem natural_real_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Filter.Tendsto (fun i => (a i : ℝ)) Filter.atTop Filter.atTop := by
  have hle : ∀ i : ℕ, (i : ℝ) ≤ (a i : ℝ) := by
    intro i
    exact_mod_cast ha.le_apply (x := i)
  exact Filter.tendsto_atTop_mono hle tendsto_natCast_atTop_atTop

theorem natural_real_gapFraction_eq (a : ℕ → ℕ) (ha : StrictMono a) (x : ℝ) :
    RealSubdivision.gapFraction (fun i => (a i : ℝ)) x = gapFraction a x := by
  have har := natural_real_strictMono ha
  by_cases hx : (a 0 : ℝ) ≤ x
  · obtain ⟨i, hi⟩ := exists_inGap ha hx
    have hir : RealSubdivision.InGap (fun i => (a i : ℝ)) x i := hi
    rw [RealSubdivision.gapFraction_eq har hir, gapFraction_eq ha hi]
  · have hlt : x < (a 0 : ℝ) := lt_of_not_ge hx
    rw [RealSubdivision.gapFraction_eq_zero_of_lt har hlt,
      gapFraction_eq_zero_of_lt ha hlt]

end SubdivisionDistribution

namespace SubdivisionDistribution
open Filter MeasureTheory
open scoped Topology

namespace RealSubdivision
/-- The historically stated subdivision hypothesis, with positive real boundaries. -/
def Admissible (a : ℕ → ℝ) : Prop :=
  StrictMono a ∧ 0 < a 0 ∧ Tendsto a atTop atTop ∧
    Tendsto (fun i => a (i + 1) / a i) atTop (𝓝 1)

noncomputable def sampled (a : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  gapFraction a (α * (n + 1 : ℕ))

def AlmostEverywhereUD (a : ℕ → ℝ) : Prop :=
  AlmostAllPositive (fun α => UniformlyDistributed (sampled a α))

/-- Original general question. Literature reports a negative answer; this file
formalizes that answer separately without asserting a proof of it. -/
def HistoricalRealQuestion : Prop :=
  ∀ a : ℕ → ℝ, Admissible a → AlmostEverywhereUD a

/-- Schmidt's negative answer in its correct real-boundary domain.
No witness or proof of Schmidt's construction is supplied. -/
def SchmidtCounterexampleStatement : Prop :=
  ∃ a : ℕ → ℝ, Admissible a ∧
    volume {α : ℝ | 0 < α ∧ ¬ UniformlyDistributed (sampled a α)} ≠ 0

theorem schmidtCounterexample_iff_not_question :
    SchmidtCounterexampleStatement ↔ ¬ HistoricalRealQuestion := by
  classical
  simp only [SchmidtCounterexampleStatement, HistoricalRealQuestion, not_forall,
    AlmostEverywhereUD]
  simp_rw [not_almostAllPositive_iff]
  simp only [exists_prop]

/-- Number of subdivision points strictly below N. For Admissible a this set
is finite, so Set.ncard has its actual finite-count meaning. -/
noncomputable def boundaryCount (a : ℕ → ℝ) (N : ℕ) : ℕ :=
  Set.ncard {i : ℕ | a i < (N : ℝ)}

theorem boundarySet_finite {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (N : ℕ) :
    Set.Finite {i : ℕ | a i < (N : ℝ)} := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ha.eventually (eventually_ge_atTop (N : ℝ)))
  apply (Set.finite_Iio K).subset
  intro i hi
  exact lt_of_not_ge (fun hik => not_lt_of_ge (hK i hik) hi)

/-- Correct primary-source sufficient growth condition, expressed with a
single positive constant and exponent uniform in N. -/
def SparseBoundaryCondition (a : ℕ → ℝ) : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop,
      (boundaryCount a N : ℝ) ≤ C * (N : ℝ) ^ (2 - δ)

/-- Davenport–Erdős1963 sufficient theorem statement, not an imported axiom
or a theorem proved in this file. -/
def DavenportErdosStatement : Prop :=
  ∀ a : ℕ → ℝ, Admissible a → SparseBoundaryCondition a → AlmostEverywhereUD a

/-- Monotonicity in either direction, as stated in the cited literature. -/
def MonotoneGaps (a : ℕ → ℝ) : Prop :=
  Monotone (fun i => a (i + 1) - a i) ∨ Antitone (fun i => a (i + 1) - a i)

/-- Davenport–LeVeque1963 sufficient theorem statement only. -/
def DavenportLeVequeStatement : Prop :=
  ∀ a : ℕ → ℝ, Admissible a → MonotoneGaps a → AlmostEverywhereUD a

theorem sampling_extension_invariant {a : ℕ → ℝ}
    {g : ℝ → ℝ} (hg : ∀ x, a 0 ≤ x → g x = gapFraction a x)
    {α : ℝ} (hα : 0 < α) :
    UniformlyDistributed (fun n => g (α * (n + 1 : ℕ))) ↔
      UniformlyDistributed (sampled a α) := by
  apply uniformlyDistributed_congr
  filter_upwards [sample_eventually_above α (a 0) hα] with n hn
  exact hg _ hn

end RealSubdivision
end SubdivisionDistribution

namespace SubdivisionDistribution
open Filter MeasureTheory
open scoped Topology

/-- The sparse-boundary hypothesis applies automatically to natural boundaries. -/
theorem natural_boundaryCount_le {a : ℕ → ℕ} (ha : StrictMono a) (N : ℕ) :
    RealSubdivision.boundaryCount (fun i => (a i : ℝ)) N ≤ N := by
  have hs : {i : ℕ | (a i : ℝ) < N} ⊆ Set.Iio N := by
    intro i hi
    have hia : i ≤ a i := ha.le_apply
    have hiN : a i < N := by exact_mod_cast hi
    exact lt_of_le_of_lt hia hiN
  have ht : (Set.Iio N).ncard = N := by
    rw [Set.ncard_eq_toFinset_card (Set.Iio N) (Set.finite_Iio N)]
    have he : (Set.finite_Iio N).toFinset = Finset.range N := by
      ext i
      simp
    rw [he, Finset.card_range]
  have hc := Set.ncard_le_ncard hs (Set.finite_Iio N)
  rw [ht] at hc
  exact hc

theorem natural_sparseBoundaryCondition {a : ℕ → ℕ} (ha : StrictMono a) :
    RealSubdivision.SparseBoundaryCondition (fun i => (a i : ℝ)) := by
  refine ⟨1, 1, by norm_num, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro N
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul]
  exact (show (RealSubdivision.boundaryCount (fun i => (a i : ℝ)) N : ℝ) ≤
    (N : ℝ) from Nat.cast_le.mpr (natural_boundaryCount_le ha N))

/-- Positive-boundary intermediate case of the explicit conditional reduction.
The full tail transfer, including an initial zero, follows below. -/
theorem nat_positive_case_of_davenportErdos
    (hDE : RealSubdivision.DavenportErdosStatement)
    {a : ℕ → ℕ} (ha : StrictMono a) (h0 : 0 < a 0) (hr : RatioTendsToOne a) :
    AlmostAllPositive (fun α => UniformlyDistributed (sampled a α)) := by
  have had : RealSubdivision.Admissible (fun i => (a i : ℝ)) :=
    ⟨natural_real_strictMono ha, Nat.cast_pos.mpr h0, natural_real_tendsto ha, hr⟩
  have he := hDE _ had (natural_sparseBoundaryCondition ha)
  apply he.mono
  intro α hα
  have hs : RealSubdivision.sampled (fun i => (a i : ℝ)) α = sampled a α := by
    funext n
    exact natural_real_gapFraction_eq a ha _
  rwa [hs] at hα

end SubdivisionDistribution

namespace SubdivisionDistribution
theorem gapFraction_shift_eq {a : ℕ → ℕ} (ha : StrictMono a) {x : ℝ}
    (hx : (a 1 : ℝ) ≤ x) :
    gapFraction (fun i => a (i + 1)) x = gapFraction a x := by
  have hzero : (a 0 : ℝ) ≤ a 1 := by exact_mod_cast ha.monotone (by omega : 0 ≤ 1)
  obtain ⟨i, hi⟩ := exists_inGap ha (hzero.trans hx)
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    exact (not_lt_of_ge hx) hi.2
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have has : StrictMono (fun i => a (i + 1)) := by
    intro k l hkl
    exact ha (by omega)
  have hjs : InGap (fun i => a (i + 1)) x j := by
    simpa [InGap, hj, Nat.add_assoc] using hi
  rw [gapFraction_eq has hjs, gapFraction_eq ha hi]
  simp only [hj, Nat.succ_eq_add_one]

end SubdivisionDistribution

namespace SubdivisionDistribution
open Filter MeasureTheory
open scoped Topology

/-- Explicit conditional reduction for every natural sequence, including one
beginning with zero. The analytic Davenport–Erdős theorem is an input. -/
theorem natQuestion_of_davenportErdos (hDE : RealSubdivision.DavenportErdosStatement) :
    NatQuestion := by
  intro a ha hr
  let b : ℕ → ℕ := fun i => a (i + 1)
  have hb : StrictMono b := by
    intro i j hij
    exact ha (Nat.add_lt_add_right hij 1)
  have hb0 : 0 < b 0 := by
    have h := ha (by omega : 0 < 1)
    dsimp [b]
    omega
  have hbr : RatioTendsToOne b := by
    apply (tendsto_add_atTop_iff_nat 1).2 hr
  have he := nat_positive_case_of_davenportErdos hDE hb hb0 hbr
  rw [almostAllPositive_iff] at he ⊢
  filter_upwards [he] with α hα
  intro hp
  have heq : sampled b α =ᶠ[atTop] sampled a α := by
    filter_upwards [sample_eventually_above α (a 1) hp] with n hn
    exact gapFraction_shift_eq ha hn
  exact (uniformlyDistributed_congr heq).1 (hα hp)

end SubdivisionDistribution
