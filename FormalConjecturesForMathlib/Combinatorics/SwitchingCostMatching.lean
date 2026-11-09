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

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.Distributions.Exponential

/-!
# Matchings with switching costs

The market model from Pittel and Rudov's
[Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x).
The worker count defaults to one more than the firm count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SwitchingCostMatching

/-- The two utilities for each firm-worker pair. `false` indexes the firm and `true` the worker. -/
abbrev Profile (n : ℕ) (w : ℕ := n + 1) := (Bool × Fin n × Fin w) → ℝ

/-- A matching assigns every firm a distinct worker. -/
abbrev Matching (n : ℕ) (w : ℕ := n + 1) := Fin n ↪ Fin w

open scoped Classical in
/-- A firm's rank counts all workers it values at least as much as the specified worker. -/
noncomputable def firmRank {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) : ℕ :=
  ∑ k : Fin w, if p (false, i, j) ≤ p (false, i, k) then 1 else 0

open scoped Classical in
/-- A worker's rank counts all firms it values at least as much as the specified firm. -/
noncomputable def workerRank {n w : ℕ} (p : Profile n w) (j : Fin w) (i : Fin n) : ℕ :=
  ∑ k : Fin n, if p (true, i, j) ≤ p (true, k, j) then 1 else 0

/-- A firm's partner rank is measurable as a function of the utility profile. -/
theorem measurable_firmRank {n w : ℕ} (i : Fin n) (j : Fin w) :
    Measurable fun p ↦ firmRank p i j := by
  unfold firmRank
  exact Finset.measurable_fun_sum _ fun k _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const

/-- A worker's partner rank is measurable as a function of the utility profile. -/
theorem measurable_workerRank {n w : ℕ} (j : Fin w) (i : Fin n) :
    Measurable fun p ↦ workerRank p j i := by
  unfold workerRank
  exact Finset.measurable_fun_sum _ fun k _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const

/-- A firm's rank is at most the number of workers. -/
theorem firmRank_le {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) :
    firmRank p i j ≤ w := by
  unfold firmRank
  calc
    _ ≤ ∑ _ : Fin w, (1 : ℕ) := Finset.sum_le_sum fun _ _ ↦ by split <;> decide
    _ = w := by simp

/-- The firms' total partner rank. -/
noncomputable def firmRankSum {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℕ :=
  ∑ i, firmRank p i (m i)

/-- The matched workers' total partner rank. Unmatched workers do not contribute. -/
noncomputable def workerRankSum {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℕ :=
  ∑ i, workerRank p (m i) i

/-- The firms' total rank is measurable as a function of the utility profile. -/
theorem measurable_firmRankSum {n w : ℕ} (m : Matching n w) :
    Measurable fun p ↦ firmRankSum p m := by
  exact Finset.measurable_fun_sum _ fun i _ ↦ measurable_firmRank i (m i)

/-- The matched workers' total rank is measurable as a function of the utility profile. -/
theorem measurable_workerRankSum {n w : ℕ} (m : Matching n w) :
    Measurable fun p ↦ workerRankSum p m := by
  exact Finset.measurable_fun_sum _ fun i _ ↦ measurable_workerRank (m i) i

/-- A pair blocks if the firm gains more than the switching cost and the worker either has no
partner or gains more than the switching cost. -/
def IsBlockingPair {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) (i : Fin n)
    (j : Fin w) : Prop :=
  j ≠ m i ∧ p (false, i, m i) + ε < p (false, i, j) ∧
    ∀ k, m k = j → p (true, k, j) + ε < p (true, i, j)

/-- A matching is stable at cost $\varepsilon$ if no pair blocks at that cost. -/
def IsStable {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) : Prop :=
  ∀ i j, ¬ IsBlockingPair p ε m i j

/-- Stability of a fixed matching is a measurable event. -/
theorem measurableSet_isStable {n w : ℕ} (ε : ℝ) (m : Matching n w) :
    MeasurableSet {p : Profile n w | IsStable p ε m} := by
  apply Measurable.setOf
  unfold IsStable IsBlockingPair
  fun_prop (disch := exact measurable_pi_apply _)

open scoped Classical in
/-- The finite set of matchings stable at the given switching cost. -/
noncomputable def stableMatchings {n w : ℕ} (p : Profile n w) (ε : ℝ) :
    Finset (Matching n w) :=
  Finset.univ.filter (IsStable p ε)

/-- The stable set is measurable as a function of the utility profile. -/
theorem measurable_stableMatchings (n w : ℕ) (ε : ℝ) :
    Measurable (fun p : Profile n w ↦ stableMatchings p ε) := by
  rw [measurable_finset_iff]
  intro m
  simpa only [stableMatchings, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq] using
    (measurableSet_isStable ε m).mem

/-- A stable matching remains stable when the switching cost increases. -/
theorem IsStable.mono {n w : ℕ} {p : Profile n w} {ε ε' : ℝ} {m : Matching n w}
    (h : IsStable p ε m) (hle : ε ≤ ε') : IsStable p ε' m := by
  intro i j hblock
  exact h i j ⟨hblock.1, (add_le_add_right hle _).trans_lt hblock.2.1, fun k hk ↦
    (add_le_add_right hle _).trans_lt (hblock.2.2 k hk)⟩

/-- The law of independent rate-one exponential utilities. -/
noncomputable def profileMeasureWithWorkers (n w : ℕ) : Measure (Profile n w) :=
  Measure.pi fun _ ↦ expMeasure 1

instance (n w : ℕ) : IsProbabilityMeasure (profileMeasureWithWorkers n w) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  unfold profileMeasureWithWorkers
  infer_instance

/-- The law of independent rate-one exponential utilities in a market with one extra worker. -/
noncomputable abbrev profileMeasure (n : ℕ) : Measure (Profile n) :=
  profileMeasureWithWorkers n (n + 1)

end SwitchingCostMatching
