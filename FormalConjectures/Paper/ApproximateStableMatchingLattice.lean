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
# Approximate lattice closure for stable matchings with switching costs

In §3 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask for a probabilistic analogue of the classical lattice of stable
matchings. The question below uses a balanced market, two uniform draws conditional on the market,
and a bound on the number of changes needed to repair both pointwise assignments.
-/

@[expose] public section

open Filter MeasureTheory SwitchingCostMatching
open scoped BigOperators Topology

namespace ApproximateStableMatchingLattice

/-- In a balanced market a matching is a permutation of the workers. -/
abbrev PerfectMatching (n : ℕ) := Equiv.Perm (Fin n)

open scoped Classical in
/-- Give each firm its preferred partner from the two matchings, favoring the first on ties. -/
noncomputable def betterAssignment {n : ℕ} (p : Profile n n) (M N : PerfectMatching n)
    (i : Fin n) : Fin n :=
  if p (false, i, N i) ≤ p (false, i, M i) then M i else N i

open scoped Classical in
/-- Give each firm its less preferred partner from the two matchings, favoring the second on ties. -/
noncomputable def worseAssignment {n : ℕ} (p : Profile n n) (M N : PerfectMatching n)
    (i : Fin n) : Fin n :=
  if p (false, i, N i) ≤ p (false, i, M i) then N i else M i

/-- An assignment can be repaired if a stable matching differs on at most $\delta n$ firms. -/
def Repairable {n : ℕ} (p : Profile n n) (ε δ : ℝ) (f : Fin n → Fin n) : Prop :=
  ∃ M : PerfectMatching n,
    IsStable p ε M.toEmbedding ∧ (hammingDist (M : Fin n → Fin n) f : ℝ) ≤ δ * (n : ℝ)

open scoped Classical in
/-- The Cartesian square of the set of matchings stable at the given switching cost. -/
noncomputable def stablePairs {n : ℕ} (p : Profile n n) (ε : ℝ) :
    Finset (PerfectMatching n × PerfectMatching n) :=
  Finset.univ.filter fun (M, N) ↦ IsStable p ε M.toEmbedding ∧ IsStable p ε N.toEmbedding

open scoped Classical in
/-- The probability that both assignments can be repaired for two independent uniform stable
matchings in the given profile. -/
noncomputable def conditionalRepairProbability {n : ℕ} (p : Profile n n) (ε δ : ℝ) : ℝ :=
  𝔼 pair ∈ stablePairs p ε,
    if Repairable p ε δ (betterAssignment p pair.1 pair.2) ∧
        Repairable p ε δ (worseAssignment p pair.1 pair.2) then 1 else 0

/-- The conditional repair probability is measurable as a function of the profile. -/
@[category API, AMS 60]
theorem measurable_conditionalRepairProbability (n : ℕ) (ε δ : ℝ) :
    Measurable (fun p : Profile n n ↦ conditionalRepairProbability p ε δ) := by
  classical
  have hStable (M : PerfectMatching n) : MeasurableSet {p | IsStable p ε M.toEmbedding} := by
    apply Measurable.setOf
    unfold IsStable IsBlockingPair
    fun_prop (disch := exact measurable_pi_apply _)
  have hAssignment (M N : PerfectMatching n) (f g : Fin n → Fin n) :
      Measurable (fun (p : Profile n n) i ↦
        if p (false, i, N i) ≤ p (false, i, M i) then f i else g i) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const
  have hRepairable {f : Profile n n → (Fin n → Fin n)} (hf : Measurable f) :
      MeasurableSet {p | Repairable p ε δ (f p)} := by
    apply Measurable.setOf
    unfold Repairable
    refine Measurable.exists fun M ↦ ?_
    have hDist : Measurable fun p ↦ (hammingDist (M : Fin n → Fin n) (f p) : ℝ) :=
      (Measurable.of_discrete (f := fun g : Fin n → Fin n ↦
        (hammingDist (M : Fin n → Fin n) g : ℝ))).comp hf
    exact (hStable M).mem.and (measurableSet_le hDist measurable_const).mem
  have hPairStable (pair : PerfectMatching n × PerfectMatching n) :
      MeasurableSet {p : Profile n n |
        IsStable p ε pair.1.toEmbedding ∧ IsStable p ε pair.2.toEmbedding} :=
    (hStable pair.1).inter (hStable pair.2)
  have hPairRepair (pair : PerfectMatching n × PerfectMatching n) :
      MeasurableSet {p | Repairable p ε δ (betterAssignment p pair.1 pair.2) ∧
        Repairable p ε δ (worseAssignment p pair.1 pair.2)} :=
    (hRepairable (hAssignment pair.1 pair.2 pair.1 pair.2)).inter
      (hRepairable (hAssignment pair.1 pair.2 pair.2 pair.1))
  unfold conditionalRepairProbability stablePairs
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_filter, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact (Finset.measurable_fun_sum _ fun pair _ ↦ Measurable.ite (hPairStable pair)
    (Measurable.ite (hPairRepair pair) measurable_const measurable_const) measurable_const).div
    (Finset.measurable_fun_sum _ fun pair _ ↦
      Measurable.ite (hPairStable pair) measurable_const measurable_const)

/-- The conditional repair probability is integrable under the profile measure. -/
@[category API, AMS 60]
theorem integrable_conditionalRepairProbability (n : ℕ) (ε δ : ℝ) :
    Integrable (fun p : Profile n n ↦ conditionalRepairProbability p ε δ)
      (profileMeasureWithWorkers n n) := by
  refine Integrable.of_bound (measurable_conditionalRepairProbability n ε δ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p ↦ ?_)
  unfold conditionalRepairProbability
  rw [Real.norm_of_nonneg (Finset.expect_nonneg fun _ _ ↦ by split <;> norm_num)]
  by_cases hs : (stablePairs p ε).Nonempty
  · exact Finset.expect_le hs fun _ _ ↦ by split <;> norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- The repair probability over both the market and the two conditional draws, at switching
cost $\log n/(6\sqrt n)$. -/
noncomputable def repairProbability (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ p, conditionalRepairProbability p (Real.log n / (6 * Real.sqrt n)) δ
    ∂profileMeasureWithWorkers n n

/-- In a balanced market with independent rate-one exponential utilities, draw two matchings
independently and uniformly conditional on the profile from the matchings stable at cost
$\varepsilon_n = \log n/(6\sqrt n)$. For each fixed $\delta>0$, does the probability tend to one
that both the firmwise better and worse assignments can be made $\varepsilon_n$-stable by
changing at most $\delta n$ partners in each? The limit uses positive market sizes $n = k+1$. -/
@[category research open, question, AMS 5 60]
theorem approximateStableMatchingLattice :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ repairProbability (k + 1) δ) atTop (𝓝 1) := by
  sorry

end ApproximateStableMatchingLattice
