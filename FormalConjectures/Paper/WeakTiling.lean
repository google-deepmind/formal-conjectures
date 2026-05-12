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
import FormalConjectures.Util.ProblemImports

/-!
# Weak tiling problems

Problems 4.1, 4.2, and 4.3 from [arxiv/2506.23631](https://arxiv.org/abs/2506.23631).

*Reference:*
* [Geometric implications of weak tiling](https://arxiv.org/abs/2506.23631)

-/

open MeasureTheory Set ENNReal NNReal

namespace WeakTiling

/-- A set `A ⊆ ℝ` is a **union of at most `n` intervals** if it can be written as a union
    of `n` order-connected sets. -/
def IsUnionOfNIntervals (n : ℕ) (A : Set ℝ) : Prop :=
  ∃ (I : Fin n → Set ℝ), (∀ i, (I i).OrdConnected) ∧ A = ⋃ i, I i

/-- A set `A ⊆ ℝ` is a **finite union of intervals** if it is a union of at most `n` intervals
    for some `n`. -/
def IsFiniteUnionOfIntervals (A : Set ℝ) : Prop :=
  ∃ n, IsUnionOfNIntervals n A

/-- A positive, locally finite Borel measure `ν` on `ℝ` is a **weak tiling measure** for a
    bounded measurable set `Ω ⊂ ℝ` if the convolution `1_Ω ∗ ν = 1_{Ωᶜ}` holds almost
    everywhere, i.e., `∫ t, 1_Ω(x - t) dν(t) = 1_{Ωᶜ}(x)` for a.e. `x ∈ ℝ`.

    This is Definition 1.1 from [arxiv/2506.23631](https://arxiv.org/abs/2506.23631). -/
def IsWeakTilingMeasure (Ω : Set ℝ) (ν : Measure ℝ) : Prop :=
  Bornology.IsBounded Ω ∧
  MeasurableSet Ω ∧
  IsLocallyFiniteMeasure ν ∧
  ∀ᵐ x ∂(volume : Measure ℝ),
    ∫ t, Ω.indicator (fun _ => (1 : ℝ)) (x - t) ∂ν =
    Ωᶜ.indicator (fun _ => (1 : ℝ)) x

/-- A **proper tiling** of `Ωᶜ` by translates of `Ω` is specified by a set of translation
    parameters `T ⊆ ℝ` such that the sum of Dirac masses on `T` is a weak tiling measure
    for `Ω`. -/
def IsProperTiling (Ω T : Set ℝ) : Prop :=
  IsWeakTilingMeasure Ω (Measure.sum (fun t : T => Measure.dirac (t : ℝ)))

/-- A set `Λ ⊆ ℝ` has **bounded density** if the number of points of `Λ` in any unit open
    interval is uniformly bounded: `sup_{x ∈ ℝ} #(Λ ∩ (x, x + 1)) < ∞`. -/
def HasBoundedDensity (Λ : Set ℝ) : Prop :=
  ∃ C : ℕ, ∀ x : ℝ, (Λ ∩ Set.Ioo x (x + 1)).Finite ∧ (Λ ∩ Set.Ioo x (x + 1)).ncard ≤ C

/-- **Problem 4.1.** Let `Ω ⊂ ℝ` be a finite union of intervals and `ν` a weak tiling
    measure for `Ω`. Must `supp(ν)` have bounded density? -/
@[category research open, AMS 42 46]
theorem problem_4_1 (Ω : Set ℝ) (hΩ : IsFiniteUnionOfIntervals Ω)
    (ν : Measure ℝ) (hν : IsWeakTilingMeasure Ω ν) : HasBoundedDensity ν.support := by
  sorry

/-- **Problem 4.2.** Let `Ω ⊂ ℝ` be a finite union of three or more intervals. If `Ω`
    weakly tiles its complement, must it also tile its complement properly? -/
@[category research open, AMS 42 46]
theorem problem_4_2 (n : ℕ) (hn : 3 ≤ n) (Ω : Set ℝ)
    (hΩ : IsUnionOfNIntervals n Ω) (ν : Measure ℝ) (hν : IsWeakTilingMeasure Ω ν) :
    ∃ T : Set ℝ, IsProperTiling Ω T := by
  sorry

/-- **Problem 4.3.** Let `Ω ⊂ ℝ` be a finite union of intervals and `ν` a weak tiling
    measure for `Ω`. Must `ν` be expressible as a convex combination of proper tiling
    measures? -/
@[category research open, AMS 42 46]
theorem problem_4_3 (Ω : Set ℝ) (hΩ : IsFiniteUnionOfIntervals Ω)
    (ν : Measure ℝ) (hν : IsWeakTilingMeasure Ω ν) :
    ∃ (T : ℕ → Set ℝ) (c : ℕ → ℝ≥0), (∀ i, IsProperTiling Ω (T i)) ∧ ∑' i : ℕ, c i = 1 ∧
    ν = Measure.sum (fun i => (c i : ℝ≥0∞) • Measure.sum (fun t : T i => Measure.dirac (t : ℝ))) := by
  sorry

end WeakTiling
