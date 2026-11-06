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
# The switching-cost hyperbola question

In §3 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask whether the classical hyperbola law extends to matchings with
switching costs. The precise question below is motivated by Figure 5 and notes 24–26 of their
[working paper](https://krudov.com/papers/JMP_Kirill_Rudov.pdf#page=25). That experiment minimizes
the matched workers' average partner rank. Here ties in that objective are broken by minimizing
the firms' average partner rank.
-/

@[expose] public section

open Filter MeasureTheory SwitchingCostMatching
open scoped Topology

namespace SwitchingCostHyperbola

open scoped Classical in
/-- The sum of the firms' partner ranks. Each rank counts all workers at least as good as the
assigned worker, including that worker. -/
noncomputable def firmRankSum {n : ℕ} (p : Profile n) (m : Matching n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin (n + 1), if p (false, i, m i) ≤ p (false, i, j) then 1 else 0

open scoped Classical in
/-- The sum of the matched workers' partner ranks. Each rank counts all firms at least as good as
the assigned firm, including that firm. -/
noncomputable def workerRankSum {n : ℕ} (p : Profile n) (m : Matching n) : ℕ :=
  ∑ i : Fin n, ∑ k : Fin n, if p (true, i, m i) ≤ p (true, k, m i) then 1 else 0

/-- A stable matching that minimizes the workers' rank sum and then the firms' rank sum. -/
def IsOptimal {n : ℕ} (p : Profile n) (ε : ℝ) (m : Matching n) : Prop :=
  IsStable p ε m ∧ ∀ m', IsStable p ε m' →
    workerRankSum p m < workerRankSum p m' ∨
      workerRankSum p m = workerRankSum p m' ∧ firmRankSum p m ≤ firmRankSum p m'

/-- A nonempty set of stable matchings has a matching that minimizes both objectives in order. -/
@[category API, AMS 5]
theorem exists_isOptimal {n : ℕ} {p : Profile n} {ε : ℝ} (h : ∃ m, IsStable p ε m) :
    ∃ m, IsOptimal p ε m := by
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image {m | IsStable p ε m}
    (fun m ↦ toLex (workerRankSum p m, firmRankSum p m)) (Set.toFinite _) h
  exact ⟨m, hm, fun m' hm' ↦ Prod.Lex.le_iff.mp (hmin m' hm')⟩

/-- Profiles for which a rank-minimizing stable matching has normalized rank product within
$\delta$ of $1$, at the switching cost used in Figure 5. -/
def goodProfiles (n : ℕ) (δ : ℝ) : Set (Profile n) :=
  {p | ∃ m, IsOptimal p (Real.log n / (6 * Real.sqrt n)) m ∧
    |(firmRankSum p m : ℝ) * workerRankSum p m / (n : ℝ) ^ 3 - 1| < δ}

/-- The rank-product event is measurable for each market size and tolerance. -/
@[category API, AMS 60]
theorem measurableSet_goodProfiles (n : ℕ) (δ : ℝ) : MeasurableSet (goodProfiles n δ) := by
  classical
  have hf (m : Matching n) : Measurable fun p ↦ firmRankSum p m := by
    unfold firmRankSum
    exact Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun j _ ↦
      Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
        measurable_const measurable_const
  have hw (m : Matching n) : Measurable fun p ↦ workerRankSum p m := by
    unfold workerRankSum
    exact Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun k _ ↦
      Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
        measurable_const measurable_const
  apply Measurable.setOf
  simp only [IsOptimal, IsStable, IsBlockingPair]
  fun_prop (disch := first | exact measurable_pi_apply _ | exact hf _ | exact hw _)

/-- In a market with $n$ firms and $n+1$ workers and independent rate-one exponential utilities,
set $\varepsilon_n = \log n/(6\sqrt n)$. Among $\varepsilon_n$-stable matchings, minimize the
matched workers' total partner rank $R_W$, breaking ties by minimizing the firms' total partner
rank $R_F$. Does $R_F R_W/n^3$ converge in probability to $1$? The limit uses positive market
sizes $n = k+1$. -/
@[category research open, question, AMS 5 60]
theorem switchingCostHyperbola :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun k : ℕ ↦ profileMeasure (k + 1) (goodProfiles (k + 1) δ)) atTop (𝓝 1) := by
  sorry

end SwitchingCostHyperbola
