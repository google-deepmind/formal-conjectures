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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Design-based network experiments

Potential outcomes satisfy arbitrary neighborhood interference. The direct treatment effect compares
treating only the focal unit with treating nobody. The two relevant exposure vectors have separate
second-moment bounds. Minimax squared-error risk ranges over every assignment distribution and every
measurable estimator, including biased estimators, and takes values in `ℝ≥0∞`.

Reference: V. Kandiros, C. Harshaw, and F. Sävje, *A Design-Based Minimax Theory for Network
Experiments*, [arXiv:2608.04909v1](https://arxiv.org/abs/2608.04909v1), Sections 2.1–2.2.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace NetworkExperiment

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Treatment indicators, one per experimental unit. -/
abbrev Assignment := ι → Bool

/-- A schedule gives every unit's real potential outcome under every assignment. -/
abbrev Schedule := Assignment ι → ι → ℝ

/-- No unit receives treatment. -/
def controlAssignment : Assignment ι := fun _ ↦ false

/-- Only the indicated unit receives treatment. -/
def singletonAssignment (i : ι) : Assignment ι := fun j ↦ decide (j = i)

variable {ι}

/-- Outcomes depend only on assignments in the unit's closed neighborhood. -/
def NeighborhoodInterference (G : SimpleGraph ι) (y : Schedule ι) : Prop :=
  ∀ i z z', (∀ j, j = i ∨ G.Adj i j → z j = z' j) → y z i = y z' i

/-- The mean direct treatment effect, comparing the singleton and empty exposures. -/
noncomputable def directEffect (y : Schedule ι) : ℝ :=
  (∑ i, y (singletonAssignment ι i) i) / Fintype.card ι -
    (∑ i, y (controlAssignment ι) i) / Fintype.card ι

/-- The estimand is the average of the unit-level exposure contrasts. -/
theorem directEffect_eq (y : Schedule ι) :
    directEffect y = (∑ i, (y (singletonAssignment ι i) i - y (controlAssignment ι) i)) /
      (Fintype.card ι : ℝ) := by
  rw [Finset.sum_sub_distrib, sub_div]
  rfl

/-- The two estimand-relevant exposure vectors each have mean square at most one. -/
def SecondMomentModel (G : SimpleGraph ι) (y : Schedule ι) : Prop :=
  NeighborhoodInterference G y ∧
    (∑ i, y (singletonAssignment ι i) i ^ 2) / (Fintype.card ι : ℝ) ≤ 1 ∧
    (∑ i, y (controlAssignment ι) i ^ 2) / (Fintype.card ι : ℝ) ≤ 1

/-- All designs and measurable, possibly biased estimators based on the observed data. -/
structure Procedure where
  design : PMF (Assignment ι)
  estimator : (Assignment ι × (ι → ℝ)) → ℝ
  measurable_estimator : Measurable estimator

/-- Expected squared error; extended nonnegative values also cover unbounded worst-case risks. -/
noncomputable def meanSquaredError (p : Procedure (ι := ι)) (y : Schedule ι) : ℝ≥0∞ :=
  ∑ z, p.design z * ENNReal.ofReal ((p.estimator (z, y z) - directEffect y) ^ 2)

/-- Worst-case risk over exactly the second-moment ANI model. -/
noncomputable def maximumRisk (G : SimpleGraph ι) (p : Procedure (ι := ι)) : ℝ≥0∞ :=
  ⨆ y : {y : Schedule ι // SecondMomentModel G y}, meanSquaredError p y.val

/-- Infimum over all assignment distributions and all measurable estimators. -/
noncomputable def minimaxRisk (G : SimpleGraph ι) : ℝ≥0∞ :=
  ⨅ p : Procedure (ι := ι), maximumRisk G p

/-- The zero schedule is in the model, so the worst-case supremum has a nonempty domain. -/
theorem zero_mem_secondMomentModel (G : SimpleGraph ι) :
    SecondMomentModel G (fun _ _ ↦ 0) := by
  simp [SecondMomentModel, NeighborhoodInterference]

/-- The schedule class contains a concrete element. -/
instance (G : SimpleGraph ι) : Nonempty {y : Schedule ι // SecondMomentModel G y} :=
  ⟨⟨fun _ _ ↦ 0, zero_mem_secondMomentModel G⟩⟩

/-- A concrete procedure with no random treatment and the identically zero estimator. -/
noncomputable def zeroProcedure : Procedure (ι := ι) where
  design := PMF.pure (controlAssignment ι)
  estimator := fun _ ↦ 0
  measurable_estimator := measurable_const

/-- The statistical procedure class is nonempty. -/
instance : Nonempty (Procedure (ι := ι)) := ⟨zeroProcedure⟩

omit [DecidableEq ι] in
/-- A mean has square at most one when the mean square is at most one. -/
theorem mean_sq_le_one (f : ι → ℝ)
    (hf : (∑ i, f i ^ 2) / (Fintype.card ι : ℝ) ≤ 1) :
    ((∑ i, f i) / (Fintype.card ι : ℝ)) ^ 2 ≤ 1 := by
  have h := sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := f)
  apply le_trans ?_ hf
  simpa using h

/-- The zero estimator has squared error at most four throughout the second-moment model. -/
theorem directEffect_sq_le_four {G : SimpleGraph ι} {y : Schedule ι}
    (hy : SecondMomentModel G y) : directEffect y ^ 2 ≤ 4 := by
  have h₁ := mean_sq_le_one _ hy.2.1
  have h₀ := mean_sq_le_one _ hy.2.2
  dsimp only [directEffect]
  nlinarith [sq_nonneg ((∑ i, y (singletonAssignment ι i) i) / (Fintype.card ι : ℝ) +
    (∑ i, y (controlAssignment ι) i) / (Fintype.card ι : ℝ))]

/-- The zero procedure's error is the square of the estimand. -/
theorem meanSquaredError_zeroProcedure (y : Schedule ι) :
    meanSquaredError zeroProcedure y = ENNReal.ofReal (directEffect y ^ 2) := by
  classical
  simp [meanSquaredError, zeroProcedure, PMF.pure_apply]

/-- The minimax value is bounded by a concrete procedure, rather than an empty infimum. -/
theorem minimaxRisk_le_four (G : SimpleGraph ι) : minimaxRisk G ≤ 4 := by
  apply (iInf_le (fun p ↦ maximumRisk G p) zeroProcedure).trans
  apply iSup_le
  intro y
  rw [meanSquaredError_zeroProcedure]
  exact (ENNReal.ofReal_le_ofReal (directEffect_sq_le_four y.property)).trans (by norm_num)

/-- In particular the extended minimax value is finite. -/
theorem minimaxRisk_ne_top (G : SimpleGraph ι) : minimaxRisk G ≠ ⊤ :=
  ne_top_of_le_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) (minimaxRisk_le_four G)

end NetworkExperiment
