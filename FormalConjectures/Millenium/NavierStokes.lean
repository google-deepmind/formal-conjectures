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

## Variable conventions

Fefferman writes the velocity as $u(x,t)$, the initial velocity as $u^\circ(x)$, the
pressure as $p(x,t)$, the force as $f(x,t)$, and the viscosity as $\nu$. In Lean,
`u₀ : ℝ^n → ℝ^n` denotes the initial velocity, while `v : ℝ^n → ℝ → ℝ^n`
denotes the solution velocity. The curried order `v x t`, `p x t`, and `f x t`
keeps the source convention that position comes before time.

Since the Clay statement gives equation (1) on the closed time half-line $t \ge 0$,
the time derivative is encoded with `derivWithin` relative to `Set.Ici 0`. The Clay
PDF also includes errata; in particular, we include spatial 1-periodicity of the
pressure in the periodic case. The sign correction to the weak-solution identity in
the errata is not represented here, since this file formalizes the four prize
alternatives rather than the later weak-solution discussion.
-/

open ContDiff Set InnerProductSpace MeasureTheory EuclideanGeometry
open scoped Laplacian

namespace NavierStokes

variable {n : ℕ}

/--
The divergence $\nabla \cdot v$ of a vector field $v : \mathbb{R}^n \to \mathbb{R}^n$
at a point $x$, computed as the trace of the Jacobian matrix.

In coordinates, $\nabla \cdot v = \sum_i \partial v_i / \partial x_i$.

This is available as the notation `∇⬝ v`. If `v` is not differentiable at `x`, then
`fderiv` is the zero map, so this definition has the corresponding junk value $0$.
-/
noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

@[inherit_doc]
notation "∇⬝" => divergence

/-- The divergence of a vector field is $0$ at points where `fderiv` has its junk value. -/
@[simp, category API, AMS 35]
theorem divergence_of_not_differentiableAt {v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : ¬ DifferentiableAt ℝ v x) : ∇⬝ v x = 0 := by
  simp [divergence, fderiv_zero_of_not_differentiableAt hv]

/-- The divergence of the zero vector field is zero. -/
@[simp, category API, AMS 35]
theorem divergence_zero (x : ℝ^n) : ∇⬝ (0 : ℝ^n → ℝ^n) x = 0 := by
  simp [divergence]

/-- The divergence of a constant vector field is zero. -/
@[simp, category API, AMS 35]
theorem divergence_const (c : ℝ^n) (x : ℝ^n) :
    ∇⬝ (fun _ : ℝ^n => c) x = 0 := by
  simp [divergence]

/-- Divergence is additive at points where both vector fields are differentiable. -/
@[category API, AMS 35]
theorem divergence_add {v w : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w x) :
    ∇⬝ (fun y => v y + w y) x = ∇⬝ v x + ∇⬝ w x := by
  sorry

/-- Divergence commutes with scalar multiplication at differentiability points. -/
@[category API, AMS 35]
theorem divergence_smul (c : ℝ) {v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x) : ∇⬝ (fun y => c • v y) x = c * ∇⬝ v x := by
  sorry

/--
A function $f : \mathbb{R}^n \to \alpha$ is 1-periodic if it is periodic in each
coordinate with period $1$, i.e. $f(x + e_i) = f(x)$ for each unit vector $e_i$.
This captures functions on the $n$-torus $\mathbb{R}^n/\mathbb{Z}^n$.
-/
def IsOnePeriodic {α : Sort*} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/--
Basic conditions on initial velocity field for the Navier-Stokes equations
in $n$-dimensional space.

The initial velocity must be:
- Divergence-free (incompressibility condition: $\nabla \cdot u_0 = 0$)
- Smooth ($C^\infty$)

These conditions apply regardless of spatial dimension.
-/
structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  /-- The initial velocity field is divergence-free (equation 2).
      This is the incompressibility constraint for the fluid. -/
  div_free : ∀ x, ∇⬝ u₀ x = 0
  /-- The initial velocity field is smooth ($C^\infty$ in all variables). -/
  smooth : ContDiff ℝ ∞ u₀

/--
Initial velocity conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

In addition to being smooth and divergence-free, the velocity must decay
faster than any polynomial at spatial infinity (condition 4 in Fefferman's paper).

This condition ensures the velocity field has finite energy and reasonable
behavior as $\lVert x \rVert \to \infty$.
-/
structure InitialVelocityConditionDecay (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  /-- All derivatives of u₀ decay faster than any polynomial (condition 4).
  For any derivative order $m$ and any decay rate $K$, there exists a constant $C$
  such that $\lVert \partial^m u_0(x) \rVert \le C/(1+\lVert x \rVert)^K$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/--
Initial velocity conditions for the periodic Navier-Stokes problem on
$\mathbb{R}^n/\mathbb{Z}^n$.

The velocity must be smooth, divergence-free, and 1-periodic in each coordinate
(condition 8, part 1 in Fefferman's paper).
-/
structure InitialVelocityConditionPeriodic (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  /-- The initial velocity is 1-periodic in each direction (condition 8, part 1). -/
  isOnePeriodic : IsOnePeriodic u₀

/--
The basic smoothness condition on the external forcing term.

The force $f(x,t)$ must be smooth ($C^\infty$) in both space and time variables
for $t \ge 0$.
-/
structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  /-- The force is smooth on $\mathbb{R}^n \times [0,\infty)$. -/
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

/--
Force conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

The force must be smooth and decay faster than any polynomial
in both space and time (condition 5 in Fefferman's paper).
-/
structure ForceConditionDecay (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  /-- All derivatives of f decay faster than any polynomial in space and time (condition 5).
  For any derivative order $m$ and any decay rate $K$, there exists $C$ such that
  $\lVert \partial^m_{x,t} f(x,t) \rVert \le C/(1+\lVert x \rVert+t)^K$ for
  $t \ge 0$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

/--
Force conditions for the periodic Navier-Stokes problem on
$\mathbb{R}^n/\mathbb{Z}^n$.

The force must be smooth, 1-periodic in space, and decay in time
(conditions 8, part 1 and 9 in Fefferman's paper).
-/
structure ForceConditionPeriodic (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  /-- The force is 1-periodic in space for all times $t \ge 0$ (condition 8, part 1). -/
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  /-- All derivatives of f decay faster than any polynomial in time (condition 9). -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

/--
A solution (v, p) to the Navier-Stokes equations in n-dimensional space
with viscosity $\nu$, initial velocity $u_0$, and external force $f$.

This structure captures the core requirements for a solution:
1. The velocity and pressure satisfy the Navier-Stokes PDE (equation 1)
2. The velocity remains divergence-free for all time (equation 2)
3. The initial condition is satisfied (equation 3)
4. The solution is smooth ($C^\infty$) for all time $t \ge 0$ (equations 6, 11)
-/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  /-- The Navier-Stokes equation (equation 1):
  $\partial v/\partial t + (v \cdot \nabla)v = \nu\Delta v - \nabla p + f$. -/
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  /-- Incompressibility constraint (equation 2): $\nabla \cdot v = 0$ for all
  $x$ and $t \ge 0$. -/
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  /-- Initial condition (equation 3): $v(x,0) = u_0(x)$ for all $x$. -/
  initial_condition : ∀ x, v x 0 = u₀ x
  /-- The velocity field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  /-- The pressure field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/--
A solution to the Navier-Stokes equations on all of $\mathbb{R}^n$ with appropriate
decay and energy bounds.

In addition to the basic solution properties, we require:
- The velocity is in $L^2$ at each time $t \ge 0$ (finite kinetic energy)
- The total energy remains bounded for all time (condition 7)
-/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is square-integrable at each time $t \ge 0$ (condition 7). -/
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  /-- The kinetic energy $\int \lVert v(x,t) \rVert^2\,dx$ remains uniformly bounded
  for all time (condition 7), where the integral is the Lebesgue integral. -/
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ^n, ‖v x t‖ ^ 2) < E

/--
A solution to the Navier-Stokes equations on the $n$-torus $\mathbb{R}^n/\mathbb{Z}^n$.

The velocity must be 1-periodic in each spatial direction for all times (condition 10).
The pressure is also required to be 1-periodic, following the errata appended to the
Clay problem statement.
-/
structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is 1-periodic in space for all times $t \ge 0$ (condition 10). -/
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  /-- The pressure is 1-periodic in space for all times $t \ge 0$ (Clay errata). -/
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)


/-- (A) Existence and smoothness of Navier–Stokes solutions on ℝ³. -/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_R3 (nu : ℝ) (hnu : nu > 0)
    (u₀ : ℝ³ → ℝ³) (hu₀ : InitialVelocityConditionDecay u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ (f := 0) v p := by
  sorry

/-- (B) Existence and smoothness of Navier–Stokes solutions in ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_existence_and_smoothness_periodic (nu : ℝ) (hnu : nu > 0)
    (u₀ : ℝ³ → ℝ³) (hu₀ : InitialVelocityConditionPeriodic u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (f := 0) v p := by
  sorry

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  sorry

/-- (D) Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³. -/
@[category research open, AMS 35]
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  sorry

end NavierStokes
