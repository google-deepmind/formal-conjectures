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
# The supercritical log-rank law for stable matchings

In §1 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask for rank asymptotics above the critical switching cost.
Lemma 5 in Appendix C of their [working paper](https://krudov.com/papers/JMP_Kirill_Rudov.pdf#page=43)
gives a joint formula for the stability and total firm rank of the diagonal matching.
The question below proposes a conditional rank limit in a balanced market.
-/

@[expose] public section

open Filter MeasureTheory Set SwitchingCostMatching
open ProbabilityTheory (cdf_eq_real cdf_expMeasure_eq expMeasure isProbabilityMeasure_expMeasure)
open scoped Topology

namespace SupercriticalStableMatchingRanks

/-- The event that the diagonal matching is stable at switching cost $\varepsilon$. -/
def diagonalStableEvent (n : ℕ) (ε : ℝ) : Set (Profile n n) :=
  {p | IsStable p ε (Function.Embedding.refl (Fin n))}

open scoped Classical in
/-- The firms' total rank in the diagonal matching. Each rank counts all workers at least as
good as the assigned worker, including the assigned worker. -/
noncomputable def diagonalFirmRankSum {n : ℕ} (p : Profile n n) : ℕ :=
  firmRankSum p (Function.Embedding.refl (Fin n))

/-- The event that the total firm rank is at most $n^{1+t}$. -/
def rankCutoffEvent (n : ℕ) (t : ℝ) : Set (Profile n n) :=
  {p | (diagonalFirmRankSum p : ℝ) ≤ (n : ℝ) ^ (1 + t)}

/-- The diagonal stability event is measurable. -/
@[category API, AMS 60]
theorem measurableSet_diagonalStableEvent (n : ℕ) (ε : ℝ) :
    MeasurableSet (diagonalStableEvent n ε) := by
  exact measurableSet_isStable ε (Function.Embedding.refl (Fin n))

/-- The total firm rank is measurable as a function of the profile. -/
@[category API, AMS 60]
theorem measurable_diagonalFirmRankSum (n : ℕ) :
    Measurable (diagonalFirmRankSum (n := n)) := by
  exact measurable_firmRankSum (Function.Embedding.refl (Fin n))

/-- The rank cutoff event is measurable. -/
@[category API, AMS 60]
theorem measurableSet_rankCutoffEvent (n : ℕ) (t : ℝ) :
    MeasurableSet (rankCutoffEvent n t) := by
  apply Measurable.setOf
  exact (Measurable.of_discrete (f := fun r : ℕ ↦ (r : ℝ) ≤ (n : ℝ) ^ (1 + t))).comp
    (measurable_diagonalFirmRankSum n)

/-- Diagonal stability has positive probability at every nonnegative switching cost. -/
@[category API, AMS 60]
theorem diagonalStableEvent_probability_pos (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < (profileMeasureWithWorkers n n).real (diagonalStableEvent n ε) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  have hInterval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
      0 < (expMeasure 1).real (Ioc a b) := by
    rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.2 hab.le) measurableSet_Iic,
      ← cdf_eq_real, ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, cdf_expMeasure_eq zero_lt_one]
    simp only [if_pos ha, if_pos (ha.trans hab.le), one_mul]
    linarith [Real.exp_lt_exp.mpr (neg_lt_neg hab)]
  let intervals (ij : Bool × Fin n × Fin n) : Set ℝ :=
    if ij.1 = true then univ else if ij.2.1 = ij.2.2 then Ioc 2 3 else Ioc 0 1
  have hsub : pi univ intervals ⊆ diagonalStableEvent n ε := by
    intro p hp i j hblock
    have hdiag := hp (false, i, i) (mem_univ _)
    have hij := hp (false, i, j) (mem_univ _)
    have hne : i ≠ j := Ne.symm hblock.1
    simp [intervals] at hdiag
    simp [intervals, hne] at hij
    have hgain : p (false, i, i) + ε < p (false, i, j) := hblock.2.1
    linarith [hdiag.1, hij.2]
  refine lt_of_lt_of_le ?_ (measureReal_mono hsub)
  unfold profileMeasureWithWorkers
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_pos fun ij _ ↦ ?_
  change 0 < (expMeasure 1).real (intervals ij)
  dsimp [intervals]
  split_ifs
  · simp
  · exact hInterval (by norm_num) (by norm_num)
  · exact hInterval (by norm_num) (by norm_num)

/-- The probability of the rank cutoff conditional on diagonal stability. -/
noncomputable def conditionalRankProbability (n : ℕ) (ε t : ℝ) : ℝ :=
  let μ := profileMeasureWithWorkers n n
  μ.real (diagonalStableEvent n ε ∩ rankCutoffEvent n t) / μ.real (diagonalStableEvent n ε)

/-- In a balanced market with independent rate-one exponential utilities, let $R_n$ be the
firms' total rank in the diagonal matching. Suppose the costs $\varepsilon_n$ are nonnegative,
$n\varepsilon_n/\log n\to+\infty$, and $2\varepsilon_n/\log n\to\rho\in[0,1)$.
For each $\rho<t<1$, does the probability of $R_n\le n^{1+t}$ conditional on the diagonal
matching being $\varepsilon_n$-stable tend to $(t-\rho)/(1-\rho)$?
The limits use sizes $n=k+2$ so that $\log n$ is positive. -/
@[category research open, question, AMS 5 60]
theorem supercriticalLogRankLaw (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Set.Ico 0 1)
    (hSupercritical : Tendsto (fun k : ℕ ↦
      let n := k + 2
      (n : ℝ) * ε n / Real.log n) atTop atTop)
    (hScale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ)) atTop (𝓝 ρ)) :
    ∀ t ∈ Set.Ioo ρ 1, Tendsto (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  sorry

end SupercriticalStableMatchingRanks
