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

This file formalizes the Clay Mathematics Institute millennium problem concerning
the existence and smoothness of solutions to the Navier-Stokes equations in three
spatial dimensions. While the definitions are generalized to arbitrary dimension n,
the millennium problem specifically concerns the case n = 3.

## References
- [Wikipedia](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness)
- [Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)

## Main Theorems (Clay Millennium Problem for n = 3)

The Clay Millennium Problem asks for a proof of one of the following four statements:

- `navier_stokes_existence_and_smoothness_R3`: (A) Global existence on ℝ³
- `navier_stokes_existence_and_smoothness_periodic`: (B) Global existence on ℝ³/ℤ³
- `navier_stokes_breakdown_R3`: (C) Existence of breakdown scenario on ℝ³
- `navier_stokes_breakdown_periodic`: (D) Existence of breakdown scenario on ℝ³/ℤ³
-/

open ContDiff Set InnerProductSpace MeasureTheory EuclideanGeometry

/--
The divergence of a vector field `v : ℝⁿ → ℝⁿ` at point `x`,
computed as the trace of the Jacobian matrix.

In coordinates: div v = Σᵢ ∂vᵢ/∂xᵢ
-/
noncomputable
def divergence {n : ℕ} (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

notation "∇⬝" => divergence

/--
A function `f : ℝⁿ → α` is periodic if it is periodic in each coordinate
with period 1, i.e., `f(x + eᵢ) = f(x)` for each unit vector `eᵢ`.
This captures functions on the n-torus ℝⁿ/ℤⁿ.
-/
def IsPeriodic {α : Sort*} {n : ℕ} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/--
Basic conditions on initial velocity field for the Navier-Stokes equations
in n-dimensional space.

The initial velocity must be:
- Divergence-free (incompressibility condition: ∇·v₀ = 0)
- Smooth (C^∞)

These conditions apply regardless of spatial dimension.
-/
structure InitialVelocityCondition {n : ℕ} (v₀ : ℝ^n → ℝ^n) : Prop where
  /-- The initial velocity field is divergence-free (equation 2).
      This is the incompressibility constraint for the fluid. -/
  div_free : ∀ x, divergence v₀ x = 0
  /-- The initial velocity field is smooth (C^∞ in all variables) -/
  smooth : ContDiff ℝ ∞ v₀

/--
Initial velocity conditions for the Navier-Stokes problem on all of ℝⁿ.

In addition to being smooth and divergence-free, the velocity must decay
faster than any polynomial at spatial infinity (condition 4 in Fefferman's paper).

This condition ensures the velocity field has finite energy and reasonable
behavior as |x| → ∞.
-/
structure InitialVelocityConditionRn {n : ℕ} (v₀ : ℝ^n → ℝ^n) : Prop
  extends InitialVelocityCondition v₀ where
  /-- All derivatives of v₀ decay faster than any polynomial (condition 4).

      For any derivative order m and any decay rate K, there exists a constant C
      such that |∂ᵐv₀(x)| ≤ C/(1+|x|)^K. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m v₀ x‖ ≤ C / (1 + ‖x‖)^K

/--
Initial velocity conditions for the periodic Navier-Stokes problem on ℝⁿ/ℤⁿ.

The velocity must be smooth, divergence-free, and periodic with period 1
in each coordinate (condition 8 in Fefferman's paper).
-/
structure InitialVelocityConditionPeriodic {n : ℕ} (v₀ : ℝ^n → ℝ^n) : Prop
  extends InitialVelocityCondition v₀ where
  /-- The initial velocity is periodic with period 1 in each direction (condition 8) -/
  periodic : IsPeriodic v₀

/--
Basic smoothness condition on external forcing term.

The force f(x,t) must be smooth (C^∞) in both space and time variables for t ≥ 0.
-/
structure ForceCondition {n : ℕ} (f : ℝ^n → ℝ → ℝ^n) : Prop where
  /-- The force is smooth on ℝⁿ × [0,∞) -/
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

/--
Force conditions for the Navier-Stokes problem on all of ℝⁿ.

The force must be smooth and decay faster than any polynomial
in both space and time (condition 5 in Fefferman's paper).
-/
structure ForceConditionRn {n : ℕ} (f : ℝ^n → ℝ → ℝ^n) : Prop
  extends ForceCondition f where
  /-- All derivatives of f decay faster than any polynomial in space and time (condition 5).

      For any derivative orders m and decay rate K, there exists C such that
      |∂ᵐ_{x,t} f(x,t)| ≤ C/(1+|x|+t)^K for t > 0.
  -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t > 0,
    ‖iteratedFDeriv ℝ m (↿f) (x,t)‖ ≤ C / (1 + ‖x‖ + t)^K

/--
Force conditions for the periodic Navier-Stokes problem on ℝⁿ/ℤⁿ.

The force must be smooth, periodic in space, and decay in time
(conditions 8-9 in Fefferman's paper).
-/
structure ForceConditionPeriodic {n : ℕ} (f : ℝ^n → ℝ → ℝ^n) : Prop
  extends ForceCondition f where
  /-- The force is periodic in space with period 1 for all times (condition 8) -/
  periodic : ∀ t ≥ 0, IsPeriodic (f · t)
  /-- All derivatives of f decay faster than any polynomial in time (condition 9). -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t > 0,
    ‖iteratedFDeriv ℝ m (↿f) (x,t)‖ ≤ C / (1 + t)^K

/--
A solution (v, p) to the Navier-Stokes equations in n-dimensional space
with viscosity nu, initial velocity v₀, and external force f.

This structure captures the core requirements for a solution:
1. The velocity and pressure satisfy the Navier-Stokes PDE (equation 1)
2. The velocity remains divergence-free for all time (equation 2)
3. The initial condition is satisfied (equation 3)
4. The solution is smooth (C^∞) for all time t ≥ 0 (equations 6, 11)
-/
structure NavierStokesExistenceAndSmoothness {n : ℕ}
    (nu : ℝ) (v₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v :  ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where

  /-- The Navier-Stokes equation (equation 1):
      ∂v/∂t + (v·∇)v = ν∆v - ∇p + f -/
  navier_stokes : ∀ x, ∀ t > 0,
    deriv (v x ·) t + fderiv ℝ (v · t) x (v x t) = nu • Δ (v · t) x - gradient (p · t) x + f x t

  /-- Incompressibility constraint (equation 2): ∇·v = 0 for all x and t ≥ 0. -/
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0

  /-- Initial condition (equation 3): v(x,0) = v₀(x) for all x. -/
  initial_condition : ∀ x, v x 0 = v₀ x

  /-- The velocity field is smooth (C^∞) on ℝⁿ × [0,∞) (conditions 6, 11). -/
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)

  /-- The pressure field is smooth (C^∞) on ℝⁿ × [0,∞) (conditions 6, 11) -/
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/--
A solution to the Navier-Stokes equations on all of ℝⁿ with appropriate
decay and energy bounds.

In addition to the basic solution properties, we require:
- The velocity is square-integrable at each time (finite kinetic energy)
- The total energy remains bounded for all time (condition 7)
-/
structure NavierStokesExistenceAndSmoothnessRn {n : ℕ}
    (nu : ℝ) (v₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v :  ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu v₀ f v p where

  /-- The velocity is square-integrable at each time t ≥ 0. -/
  integrable : ∀ t ≥ 0, Integrable (‖v · t‖^2)

  /-- The kinetic energy ∫|v(x,t)|²dx remains uniformly bounded for all time (condition 7). -/
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ^n, ‖v x t‖^2) < E


/--
A solution to the Navier-Stokes equations on the n-torus ℝⁿ/ℤⁿ.

The velocity and pressure must be periodic with period 1 in each
spatial direction for all times (condition 10).
-/
structure NavierStokesExistenceAndSmoothnessPeriodic {n : ℕ}
    (nu : ℝ) (v₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v :  ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu v₀ f v p where

  /-- The velocity is periodic in space with period 1 for all times t ≥ 0 (condition 10). -/
  velocity_periodic : ∀ t ≥ 0, IsPeriodic (v · t)

  /-- The pressure is periodic in space with period 1 for all times t ≥ 0 (condition 10). -/
  pressure_periodic : ∀ t ≥ 0, IsPeriodic (p · t)


/-- (A) Existence and smoothness of Navier–Stokes solutions on ℝ³. -/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_R3 (nu : ℝ) (hnu : nu > 0)
  (v₀ : ℝ³ → ℝ³) (hv₀ : InitialVelocityConditionRn v₀) :
  ∃ v p, NavierStokesExistenceAndSmoothnessRn (n:=3) nu v₀ (f:=0) v p := sorry

/-- (B) Existence and smoothness of Navier–Stokes solutions in ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_periodic (nu : ℝ) (hnu : nu > 0)
  (v₀ : ℝ³ → ℝ³) (hv₀ : InitialVelocityConditionPeriodic v₀) :
  ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic (n:=3) nu v₀ (f:=0) v p := sorry

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
  ∃ (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionRn v₀ ∧ ForceConditionRn f ∧
    ¬(∃ v p, NavierStokesExistenceAndSmoothnessRn (n:=3) nu v₀ f v p) := sorry

/-- (D) Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
  ∃ (v₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic v₀ ∧ ForceConditionPeriodic f ∧
    ¬(∃ v p, NavierStokesExistenceAndSmoothnessPeriodic (n:=3) nu v₀ f v p) := sorry
