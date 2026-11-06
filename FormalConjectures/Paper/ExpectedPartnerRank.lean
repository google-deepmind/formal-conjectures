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
# Expected partner rank under switching costs

In §3 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask how a firm's expected partner rank depends on the switching
cost when the matching is sampled uniformly from the stable set. The question below specifies a
market with one extra worker and asks whether the expectation over random markets is nondecreasing
in the cost.
-/

@[expose] public section

open MeasureTheory SwitchingCostMatching
open scoped BigOperators

namespace ExpectedPartnerRank

open scoped Classical in
/-- All matchings in the profile that are stable at cost $\varepsilon$. -/
noncomputable def stableMatchings {n : ℕ} (p : Profile n) (ε : ℝ) : Finset (Matching n) :=
  Finset.univ.filter (IsStable p ε)

/-- The mean rank of firm $i$'s partner under the uniform distribution on the profile's stable
matchings. The stable set is nonempty at nonnegative costs by classical stable matching
existence and monotonicity of stability. -/
noncomputable def conditionalMeanRank {n : ℕ} (i : Fin n) (ε : ℝ) (p : Profile n) : ℝ :=
  𝔼 m ∈ stableMatchings p ε, (firmRank p i (m i) : ℝ)

/-- The conditional mean rank is measurable as a function of the profile. -/
@[category API, AMS 60]
theorem measurable_conditionalMeanRank {n : ℕ} (i : Fin n) (ε : ℝ) :
    Measurable (conditionalMeanRank i ε) := by
  classical
  have hStable (m : Matching n) : MeasurableSet {p | IsStable p ε m} := by
    apply Measurable.setOf
    unfold IsStable IsBlockingPair
    fun_prop (disch := exact measurable_pi_apply _)
  unfold conditionalMeanRank stableMatchings
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_filter, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact (Finset.measurable_fun_sum _ fun m _ ↦ Measurable.ite (hStable m)
    (Measurable.of_discrete.comp (measurable_firmRank i (m i))) measurable_const).div
    (Finset.measurable_fun_sum _ fun m _ ↦
      Measurable.ite (hStable m) measurable_const measurable_const)

/-- The conditional mean rank is integrable under the law of random profiles. -/
@[category API, AMS 60]
theorem integrable_conditionalMeanRank {n : ℕ} (i : Fin n) (ε : ℝ) :
    Integrable (conditionalMeanRank i ε) (profileMeasure n) := by
  refine Integrable.of_bound (measurable_conditionalMeanRank i ε).aestronglyMeasurable (n + 1)
    (Filter.Eventually.of_forall fun p ↦ ?_)
  unfold conditionalMeanRank
  rw [Real.norm_of_nonneg (Finset.expect_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
  by_cases h : (stableMatchings p ε).Nonempty
  · exact Finset.expect_le h fun m _ ↦ by exact_mod_cast firmRank_le p i (m i)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp
    positivity

/-- The expected rank obtained by first sampling the profile and then sampling uniformly from
its stable matchings. -/
noncomputable def expectedPartnerRank {n : ℕ} (i : Fin n) (ε : ℝ) : ℝ :=
  ∫ p, conditionalMeanRank i ε p ∂profileMeasure n

/-- For every positive $n$, in a market with $n$ firms and $n+1$ workers and independent rate-one
exponential utilities, is the first firm's expected partner rank nondecreasing in the
nonnegative switching cost? The matching is sampled uniformly conditional on the profile. -/
@[category research open, question, AMS 5 60]
theorem expectedPartnerRank_monotone :
    ∀ k : ℕ, MonotoneOn (expectedPartnerRank (0 : Fin (k + 1))) (Set.Ici 0) := by
  sorry

end ExpectedPartnerRank
