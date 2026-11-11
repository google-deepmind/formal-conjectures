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

public import FormalConjecturesForMathlib.Geometry.Euclidean
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

/-!
# Spherical cap discrepancy
-/

@[expose] public section

open MeasureTheory
open scoped EuclideanGeometry

namespace SphericalCap

/-- The unit sphere $S^2\subseteq\mathbb{R}^3$. -/
abbrev Sphere : Type := Metric.sphere (0 : ℝ^ 3) 1

/-- The spherical cap $\{x\in S^2 : \langle x,u\rangle\geq t\}$ with centre `u` and inner-product
threshold `t ∈ [-1, 1]`. -/
def cap (u : Sphere) (t : ℝ) : Set Sphere :=
  {x | t ≤ inner ℝ (x : ℝ^ 3) (u : ℝ^ 3)}

/-- The surface measure on the unit sphere, induced by Lebesgue measure on $\mathbb{R}^3$. -/
noncomputable def surface : Measure Sphere :=
  (volume : Measure (ℝ^ 3)).toSphere

/-- The normalised surface measure $\alpha_C$ of a subset `C` of the sphere, so that the entire
sphere has measure $1$. -/
noncomputable def normalizedArea (C : Set Sphere) : ℝ :=
  (surface C).toReal / (surface Set.univ).toReal

open scoped Classical in
/-- The spherical cap discrepancy
$$D(P) = \max_C \lvert \lvert C\cap P\rvert - \alpha_C \lvert P\rvert \rvert$$
of a finite set `P ⊆ S²`, where the maximum is taken over all spherical caps $C$ and
$\alpha_C$ is the normalised surface measure of $C$. -/
noncomputable def discrepancy (P : Finset Sphere) : ℝ :=
  sSup {r | ∃ (u : Sphere) (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 ∧
    r = |((P.filter (· ∈ cap u t)).card : ℝ) - normalizedArea (cap u t) * P.card|}

/-- The minimal spherical cap discrepancy $\min_{\lvert P\rvert=n}D(P)$ of an `n`-point subset
of the sphere. -/
noncomputable def minDiscrepancy (n : ℕ) : ℝ :=
  sInf {d | ∃ P : Finset Sphere, P.card = n ∧ d = discrepancy P}

/-- Every cap is closed and hence measurable for surface measure. -/
theorem measurableSet_cap (u : Sphere) (t : ℝ) : MeasurableSet (cap u t) := by
  exact (isClosed_le continuous_const
    (Continuous.inner continuous_subtype_val continuous_const)).measurableSet

/-- Normalised area is nonnegative, also for the empty set. -/
theorem normalizedArea_nonneg (C : Set Sphere) : 0 ≤ normalizedArea C := by
  unfold normalizedArea
  positivity

/-- No subset has greater normalised area than the whole sphere. -/
theorem normalizedArea_le_one (C : Set Sphere) : normalizedArea C ≤ 1 := by
  let : IsFiniteMeasure surface := by unfold surface; infer_instance
  have hmono : (surface C).toReal ≤ (surface Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top surface Set.univ) (measure_mono (Set.subset_univ C))
  exact div_le_one_of_le₀ hmono ENNReal.toReal_nonneg

open scoped Classical in
/-- Every individual cap has counting error at most the sample size. -/
theorem capError_le_card (P : Finset Sphere) (u : Sphere) (t : ℝ) :
    |((P.filter (· ∈ cap u t)).card : ℝ) - normalizedArea (cap u t) * P.card| ≤ P.card := by
  classical
  have hf : ((P.filter (· ∈ cap u t)).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_filter_le P (· ∈ cap u t)
  have hf0 : (0 : ℝ) ≤ (P.filter (· ∈ cap u t)).card := by positivity
  have hn : (0 : ℝ) ≤ P.card := by positivity
  have ha0 := normalizedArea_nonneg (cap u t)
  have ha1 := normalizedArea_le_one (cap u t)
  rw [abs_le]
  constructor <;> nlinarith

/-- Cap discrepancy is finite and bounded by the number of points. -/
theorem discrepancy_le_card (P : Finset Sphere) : discrepancy P ≤ P.card := by
  classical
  have hne : Nonempty Sphere := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : ℝ^ 3))).mpr
      (by norm_num : (0 : ℝ) ≤ 1)
    exact ⟨⟨x, hx⟩⟩
  let u : Sphere := Classical.choice hne
  apply csSup_le
  · exact ⟨_, u, 0, by norm_num, rfl⟩
  · rintro r ⟨v, t, ht, rfl⟩
    exact capError_le_card P v t

end SphericalCap
