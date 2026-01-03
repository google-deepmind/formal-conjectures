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
# Existence And Smoothness Of The Navier–Stokes Equation

*Reference:*
  [Wikipedia](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness)
  [Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
-/

open ContDiff Set InnerProductSpace MeasureTheory

local macro "ℝ³"  : term => `(EuclideanSpace ℝ (Fin 3))

noncomputable
def div (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ := (fderiv ℝ v x).trace ℝ ℝ³

def IsPeriodic {α : Sort*} (f : ℝ³ → α) : Prop := ∀ x i, f (x + EuclideanSpace.single i 1) = f x

structure InitialVelocityCondition (v₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, div v₀ x = 0
  smooth : ContDiff ℝ ∞ v₀

structure InitialVelocityConditionR3 (v₀ : ℝ³ → ℝ³) : Prop
  extends InitialVelocityCondition v₀ where
  decay : ∀ n : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n v₀ x‖ ≤ C / (1 + ‖x‖)^K

structure InitialVelocityConditionPeriodic (v₀ : ℝ³ → ℝ³) : Prop
  extends InitialVelocityCondition v₀ where
  periodic : IsPeriodic v₀

structure ForceCondition (f : ℝ³ → ℝ → ℝ³) : Prop where
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

structure ForceConditionR3 (f : ℝ³ → ℝ → ℝ³) : Prop
  extends ForceCondition f where
  decay : ∀ n : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDeriv ℝ n (↿f) (x,t)‖ ≤ C / (1 + ‖x‖ + t)^K

structure ForceConditionPeriodic (f : ℝ³ → ℝ → ℝ³) : Prop
  extends ForceCondition f where
  periodic : ∀ t ≥ 0, IsPeriodic (f · t)
  decay : ∀ n : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDeriv ℝ n (↿f) (x,t)‖ ≤ C / (1 + t)^K


structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v :  ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where

  navierStokes : ∀ x, ∀ t ≥ 0,
    deriv (v x ·) t + fderiv ℝ (v · t) x (v x t) = nu • Δ (v · t) x - gradient (p · t) x + f x t
    ∧
    div (v · t) x = 0

  initialCondition : ∀ x, v x 0 = v₀ x

  velocitySmoothness : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressureSmoothness : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)


structure NavierStokesExistenceAndSmoothnessR3
    (nu : ℝ) (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v :  ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu v₀ f v p where

  integrable : ∀ t ≥ 0, Integrable (‖v · t‖^2)
  globallyBoundedEnergy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖^2) < E

structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v :  ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu v₀ f v p where

  periodic : ∀ t ≥ 0, IsPeriodic (v · t)


/-- (A) Existence and smoothness of Navier–Stokes solutions on ℝ³.
-/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_R3 (nu : ℝ) (hnu : nu > 0)
  (v₀ : ℝ³ → ℝ³) (hv₀ : InitialVelocityConditionR3 v₀) :
  ∃ v p, NavierStokesExistenceAndSmoothnessR3 nu v₀ (f:=0) v p := sorry

/-- (B) Existence and smoothness of Navier–Stokes solutions in ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_periodic (nu : ℝ) (hnu : nu > 0)
  (v₀ : ℝ³ → ℝ³) (hv₀ : InitialVelocityConditionPeriodic v₀) :
  ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu v₀ (f:=0) v p := sorry

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³.-/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
  ∃ (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionR3 v₀ → ForceConditionR3 f →
    ¬(∃ v p, NavierStokesExistenceAndSmoothnessR3 nu v₀ f v p) := sorry

/-- (D) Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
  ∃ (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic v₀ → ForceConditionPeriodic f →
    ¬(∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu v₀ f v p) := sorry
