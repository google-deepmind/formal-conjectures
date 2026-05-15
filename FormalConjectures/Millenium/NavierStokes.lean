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
# Existence and Smoothness of the Navier–Stokes Equation (Clay Millennium Problem)

The Clay Mathematics Institute's Navier–Stokes Millennium Problem, as stated by
Fefferman (2000) with the 2001 erratum applied. The problem comprises four
routes — any one of which, if proven, wins the prize:

- **Route A** — existence and smoothness on `ℝ³` for arbitrary Schwartz initial
  data and zero applied force.
- **Route B** — existence and smoothness on `T³` for arbitrary smooth periodic
  initial data and zero applied force.
- **Route C** — breakdown: exhibit initial data and an applied force on `ℝ³`
  for which no globally smooth solution exists.
- **Route D** — breakdown on `T³` for periodic initial data and applied force.

The formalisation is classical pointwise everywhere: velocity `u` and pressure
`p` are `C^∞` on `ℝ³ × [0, ∞)`, and every equation is asserted by pointwise
`Eq`. The time domain `[0, ∞)` is the named set `TimeDomain := Set.Ici 0`.

## Newton's-law decomposition

Following Fefferman p.1 l.27–28, the symbol `f` in the Clay statement denotes
the external/applied force only. The pressure-gradient `-∇p` and viscous `νΔu`
terms are forces in the Newton's-law decomposition but are reconstructed from
`p` and `u`. We write `f_applied` for the external force throughout.

```
   ∂_t u + (u·∇) u   =   -∇p   +   νΔu   +   f_applied
   └──────┬──────┘       └─┬─┘   └─┬─┘     └───┬────┘
   total acceleration     pressure viscous     applied
   of fluid element       force    force       (external) force
```

## Namespace discipline

Every reference to a locally-defined identifier is fully qualified with the
`NavierStokesMillennium.` prefix at the use site.

## Cross-disciplinary disambiguation

Cross-disciplinary disambiguation of the Clay PDF's English-language narrative
follows the typed-ledger discipline of Charlton (2026), which reconciles the
Systems-Engineering reading of the specification with PDE-sector conventions
(Lebesgue vs. Riemann integration assumptions, gauge conventions, the
external-versus-net-force terminology distinction, and the implicit time
domain `t ≥ 0`).

*References:*
- Fefferman, C. L. *Existence and Smoothness of the Navier–Stokes Equation.*
  Clay Mathematics Institute Millennium Problem statement, 2000.
  [Clay PDF](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
- Fefferman, C. L. *Errata to "Existence and Smoothness of the Navier–Stokes
  Equation"*, 2001 (corrections to Eqs. (8) and (12)).
- Charlton, J. P., Jr. *Enabling Cross-Silo Innovation for the CPNS: A Public
  Specification Resolving Ambiguity.* Zenodo, 2026.
  DOI: [10.5281/zenodo.18517686](https://doi.org/10.5281/zenodo.18517686)
-/

/-
@(#) Author: Paul Charlton -- techguru@byiq.com, for Research ByIQ LLC.
-/

open MeasureTheory

namespace NavierStokesMillennium

/- ## Section 1 — Manifold

### Variable typings

```
ν          : ℝ                       -- kinematic viscosity
n          : ℕ                       -- spatial dimension
t          : ℝ                       -- time
x          : Space 3                 -- spatial point
u          : Space 3 → ℝ → Space 3   -- velocity field
p          : Space 3 → ℝ → ℝ         -- pressure field (scalar)
f_applied  : Space 3 → ℝ → Space 3   -- applied (external) force
u₀         : Space 3 → Space 3       -- initial velocity
```

### Conventions

| #   | Name                 | Convention | Source |
|-----|----------------------|------------|--------|
| C1  | spatial measure      | `(volume : Measure (Space 3))` is the product Lebesgue measure on `EuclideanSpace ℝ (Fin 3)` via `MeasureTheory.Measure.pi` | implicit; Fefferman p.1 l.47–48 uses `dx` without naming the measure |
| C2  | time measure         | `(volume : Measure ℝ)` is Lebesgue on `ℝ` | implicit |
| C3  | spacetime measure    | `(volume : Measure (Space 3 × ℝ))` is `volume.prod volume` | implicit; Fefferman p.3 l.27 uses `dxdt` without naming |
| C4  | equality regime      | every `=` in classical-route statements is `Eq` (pointwise) | implicit; PDE-dialect default for `C^∞` routes |
| C5  | pressure ontology    | `p` is a function `Space 3 → ℝ → ℝ`, not a gauge equivalence class. On `T³`, prior `P5_5` imposes the PDE-community zero-mean gauge convention, which Fefferman did not write and which is mathematically inert | implicit; classical routes |
| C6  | time domain          | every time-quantified prior asserts `t ∈ TimeDomain`; every smoothness predicate uses `ContDiffOn ℝ ⊤ … Spacetime` | Fefferman p.1 l.5, eqs. (1)/(2) parentheticals, eq. (6), eqs. (9)–(11), statements (C)/(D) |
| C7  | uniqueness           | only existence is asserted (`∃`, not `∃!`); breakdown routes negate existence with `¬ ∃` | Fefferman: "there exist smooth functions" / "there exist no solutions" |
| C8  | dimension fixed      | `n = 3` for the prize problems A–D | Fefferman p.2 l.13: "Take ν > 0 and n = 3" |
| C9  | force terminology    | the symbol `f` (here `f_applied`) is the external/applied force; pressure-gradient and viscous forces are separate | Fefferman p.1 l.27–28 |
| C10 | namespace discipline | every reference to a locally-defined identifier is fully qualified with the `NavierStokesMillennium.` prefix at the use site | repo convention |
-/

/-- Spatial carrier: `n`-dimensional Euclidean space.

SOURCE: Fefferman p.1 l.1–4 (ambient `R^n`). -/
abbrev Space (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The `j`-th standard basis vector `e_j`.

SOURCE: Fefferman p.1 l.50: "`e_j` = `j`-th unit vector in `R^n`". -/
noncomputable abbrev e {n : ℕ} (j : Fin n) : NavierStokesMillennium.Space n :=
  EuclideanSpace.single j 1

/-- The Clay Navier–Stokes time domain `[0, ∞)`.

SOURCE: Fefferman p.1 l.5 ("`t ≥ 0`"), eqs. (1), (2) parentheticals
("`x ∈ ℝⁿ, t ≥ 0`"), eq. (5) ("on `ℝⁿ × [0, ∞)`"), eq. (6)
("`p, u ∈ C^∞(ℝⁿ × [0, ∞))`"), eq. (7) ("for all `t ≥ 0`"), eqs. (9), (10)
("on `ℝ³ × [0, ∞)`"), eq. (11) ("`p, u ∈ C^∞(ℝⁿ × [0, ∞))`"), statements (C),
(D) ("no solutions ... on `ℝ³ × [0, ∞)`"). -/
def TimeDomain : Set ℝ := Set.Ici 0

/-- The Clay Navier–Stokes spacetime carrier `ℝ³ × [0, ∞)`.

SOURCE: product of `Space 3` and `TimeDomain`. -/
def Spacetime : Set (NavierStokesMillennium.Space 3 × ℝ) :=
  Set.univ ×ˢ NavierStokesMillennium.TimeDomain

/-- Divergence of a vector field.

SOURCE: Fefferman eq. (2), p.1 l.20–21:
"`div u = ∑_{i=1}^n ∂u_i/∂x_i`". -/
noncomputable def divergence {n : ℕ}
    (u : NavierStokesMillennium.Space n → NavierStokesMillennium.Space n)
    (x : NavierStokesMillennium.Space n) : ℝ :=
  ∑ i : Fin n, (fderiv ℝ u x (NavierStokesMillennium.e i)) i

/-- Gradient of a scalar field (vector of first partials).

SOURCE: Fefferman eq. (1), p.1 l.13–17 (the `∂p/∂x_i` term). -/
noncomputable def gradientScalar {n : ℕ}
    (f_scalar : NavierStokesMillennium.Space n → ℝ)
    (x : NavierStokesMillennium.Space n) : NavierStokesMillennium.Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i : Fin n => fderiv ℝ f_scalar x (NavierStokesMillennium.e i))

/-- Componentwise vector Laplacian.

SOURCE: Fefferman eq. (1), p.1 l.13–17, with `Δ` defined p.1 l.18–19:
"`Δ = ∑_{i=1}^n ∂²/∂x_i²`". -/
noncomputable def vectorLaplacian {n : ℕ}
    (u : NavierStokesMillennium.Space n → NavierStokesMillennium.Space n)
    (x : NavierStokesMillennium.Space n) : NavierStokesMillennium.Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i : Fin n =>
      ∑ j : Fin n,
        fderiv ℝ (fun y => fderiv ℝ (fun z => (u z) i) y
          (NavierStokesMillennium.e j)) x (NavierStokesMillennium.e j))

/-- Convective term `(u · ∇) u` (the LHS nonlinearity of the momentum equation).

SOURCE: Fefferman eq. (1), p.1 l.13–17: "`∑_{j=1}^n u_j ∂u_i/∂x_j`". -/
noncomputable def convective {n : ℕ}
    (u : NavierStokesMillennium.Space n → NavierStokesMillennium.Space n)
    (x : NavierStokesMillennium.Space n) : NavierStokesMillennium.Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i : Fin n =>
      ∑ j : Fin n, (u x) j *
        fderiv ℝ (fun y => (u y) i) x (NavierStokesMillennium.e j))

/-- Partial time derivative of a time-dependent vector field.

SOURCE: Fefferman eq. (1), p.1 l.13: "`(∂/∂t) u_i`". -/
noncomputable def partialT {n : ℕ}
    (u : NavierStokesMillennium.Space n → ℝ → NavierStokesMillennium.Space n)
    (x : NavierStokesMillennium.Space n) (t : ℝ) :
    NavierStokesMillennium.Space n :=
  deriv (fun s : ℝ => u x s) t

/-- Iterated mixed spatial-temporal derivative norm, used to express
Schwartz-class decay of initial data and applied force.

SOURCE: Fefferman eqs. (4), (5), (9), pp.1–2. -/
noncomputable def spatiotemporalNorm {n : ℕ} (k m : ℕ)
    (g : NavierStokesMillennium.Space n → ℝ → NavierStokesMillennium.Space n)
    (x : NavierStokesMillennium.Space n) (t : ℝ) : ℝ :=
  ‖iteratedFDeriv ℝ k
    (fun y : NavierStokesMillennium.Space n => iteratedDeriv m (g y) t) x‖

/-- Classical pointwise Navier–Stokes momentum equation.

SOURCE: Fefferman eq. (1), p.1 l.13–17. -/
def NSMomentumPt (ν : ℝ)
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ)
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (x : NavierStokesMillennium.Space 3) (t : ℝ) : Prop :=
  NavierStokesMillennium.partialT u x t
      + NavierStokesMillennium.convective (fun y => u y t) x =
    ν • NavierStokesMillennium.vectorLaplacian (fun y => u y t) x   -- viscous force
    - NavierStokesMillennium.gradientScalar (fun y => p y t) x      -- pressure force
    + f_applied x t                                                 -- applied (external) force

/-- The fundamental period cube `[0, 1)³`.

SOURCE: standard periodic-class domain on `T³`. -/
def unitCube : Set (NavierStokesMillennium.Space 3) :=
  { x | ∀ i : Fin 3, x i ∈ Set.Ico (0 : ℝ) 1 }

/-- Classical weak-formulation identity (Fefferman eq. (12), with the sign
correction from the 2001 erratum applied).

SOURCE: Fefferman p.3 l.23–30, corrected per erratum p.5. -/
def NSWeakIdentity (ν : ℝ)
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ)
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (θ : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3),
    ContDiff ℝ ⊤ (Function.uncurry θ) →
    HasCompactSupport (Function.uncurry θ) →
    - (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
          inner ℝ (u xt.1 xt.2) (NavierStokesMillennium.partialT θ xt.1 xt.2))
    - (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
        ∑ i : Fin 3, ∑ j : Fin 3,
          (u xt.1 xt.2) i * (u xt.1 xt.2) j
            * fderiv ℝ (fun y => (θ y xt.2) i) xt.1
                (NavierStokesMillennium.e j))
    = ν • (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
            inner ℝ (u xt.1 xt.2)
              (NavierStokesMillennium.vectorLaplacian
                (fun y => θ y xt.2) xt.1))
      + (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
          inner ℝ (f_applied xt.1 xt.2) (θ xt.1 xt.2))
      + (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
          (p xt.1 xt.2) *
            NavierStokesMillennium.divergence (fun y => θ y xt.2) xt.1)

/- ### Priors -/

/-- **P1.1** — dimension three.

SOURCE: Fefferman p.2 l.13: "Take `ν > 0` and `n = 3`." -/
def P1_1 : Prop := (3 : ℕ) = 3

/-- **P1.2** — viscosity strictly positive.

SOURCE: Fefferman p.2 l.13: "Take `ν > 0` and `n = 3`." -/
def P1_2 (ν : ℝ) : Prop := 0 < ν

/-- **P1.3** — initial data smooth.

SOURCE: Fefferman p.1 l.39 / p.2 l.3: "`u₀` is smooth". -/
def P1_3 (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ContDiff ℝ ⊤ u₀

/-- **P1.4** — initial data divergence-free.

SOURCE: Fefferman eq. (2) applied at `t = 0`, p.1 l.20–23. -/
def P1_4 (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ x : NavierStokesMillennium.Space 3, NavierStokesMillennium.divergence u₀ x = 0

/-- **P2.1** — pointwise Navier–Stokes momentum equation on `Space 3 × TimeDomain`.

SOURCE: Fefferman eq. (1), p.1 l.13–17. -/
def P2_1 (ν : ℝ)
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ)
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
    t ∈ NavierStokesMillennium.TimeDomain →
    NavierStokesMillennium.NSMomentumPt ν u p f_applied x t

/-- **P2.2** — pointwise incompressibility.

SOURCE: Fefferman eq. (2), p.1 l.20–21:
"`div u = ∑_{i=1}^n ∂u_i/∂x_i = 0`". -/
def P2_2
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
    t ∈ NavierStokesMillennium.TimeDomain →
    NavierStokesMillennium.divergence (fun y => u y t) x = 0

/-- **P2.3** — initial condition `u(x, 0) = u₀(x)`.

SOURCE: Fefferman eq. (3), p.1 l.23. -/
def P2_3
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ x : NavierStokesMillennium.Space 3, u x 0 = u₀ x

/-- **P3.1** — initial data Schwartz decay.

SOURCE: Fefferman eq. (4), p.1 l.39–40:
"`|∂_x^α u₀(x)| ≤ C_{α K} (1+|x|)^{-K}` on `R^n`, for any `α` and `K`". -/
def P3_1 (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (k K : ℕ), ∃ (C : ℝ), ∀ x : NavierStokesMillennium.Space 3,
    ‖iteratedFDeriv ℝ k u₀ x‖ ≤ C * (1 + ‖x‖)^(-(K : ℝ))

/-- **P3.2** — applied-force Schwartz decay in space and time.

SOURCE: Fefferman eq. (5), p.1 l.41–42:
"`|∂_x^α ∂_t^m f(x,t)| ≤ C_{α m K} (1+|x|+t)^{-K}` on `R^n × [0, ∞)`". -/
def P3_2
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (k m K : ℕ), ∃ (C : ℝ),
    ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
      t ∈ NavierStokesMillennium.TimeDomain →
      NavierStokesMillennium.spatiotemporalNorm k m f_applied x t
        ≤ C * (1 + ‖x‖ + t)^(-(K : ℝ))

/-- **P3.3** — applied force `C^∞` on `ℝ³ × [0, ∞)`.

SOURCE: Fefferman p.2 statement (C): "smooth `f(x,t)` on `ℝ³ × [0, ∞)`",
p.2 l.27–29. -/
def P3_3
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry f_applied) NavierStokesMillennium.Spacetime

/-- **P4.1** — initial data periodic in each coordinate direction.

SOURCE: Fefferman eq. (8) first half, p.1 l.49–51: "`u₀(x + e_j) = u₀(x)`". -/
def P4_1 (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (j : Fin 3),
    u₀ (x + NavierStokesMillennium.e j) = u₀ x

/-- **P4.2** — applied force periodic in each coordinate direction.

SOURCE: Fefferman eq. (8) second half, p.1 l.49–51:
"`f(x + e_j, t) = f(x, t)`". -/
def P4_2
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ) (j : Fin 3),
    f_applied (x + NavierStokesMillennium.e j) t = f_applied x t

/-- **P4.3** — initial pressure periodic in each coordinate direction.

SOURCE: Fefferman 2001 erratum, p.5: "the further condition
`p(x + e_j, t) = p(x, t)` should be made explicit in Eqn (8)". -/
def P4_3 (p : NavierStokesMillennium.Space 3 → ℝ → ℝ) : Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ) (j : Fin 3),
    p (x + NavierStokesMillennium.e j) t = p x t

/-- **P4.4** — applied-force time decay on the torus.

SOURCE: Fefferman eq. (9), p.2 l.4–5:
"`|∂_x^α ∂_t^m f(x,t)| ≤ C_{α m K} (1+t)^{-K}` on `T^n × [0, ∞)`". -/
def P4_4
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (k m K : ℕ), ∃ (C : ℝ),
    ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
      t ∈ NavierStokesMillennium.TimeDomain →
      NavierStokesMillennium.spatiotemporalNorm k m f_applied x t
        ≤ C * (1 + t)^(-(K : ℝ))

/-- **P4.5** — initial data `C^∞` (periodic-route restatement of P1.3).

SOURCE: Fefferman p.2 l.3: "`u₀` is smooth". -/
def P4_5 (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3) :
    Prop :=
  ContDiff ℝ ⊤ u₀

/-- **P5.1** — global `C^∞` regularity of `(u, p)` on `ℝ³ × [0, ∞)`.

SOURCE: Fefferman eq. (6), p.1 l.44. Applies to Routes A and C. -/
def P5_1
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤
      (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
      NavierStokesMillennium.Spacetime
    ∧ ContDiffOn ℝ ⊤
        (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
        NavierStokesMillennium.Spacetime

/-- **P5.2** — solution velocity periodic on `ℝ³ × [0, ∞)`.

SOURCE: Fefferman eq. (10), p.2 l.7–8:
"`u(x + e_j, t) = u(x, t)` on `ℝ³ × [0, ∞)`". Applies to Routes B and D. -/
def P5_2
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
    t ∈ NavierStokesMillennium.TimeDomain →
    ∀ (j : Fin 3), u (x + NavierStokesMillennium.e j) t = u x t

/-- **P5.3** — global `C^∞` regularity of `(u, p)` on `T³ × [0, ∞)`.

SOURCE: Fefferman eq. (11), p.2 l.10–11. Applies to Routes B and D. -/
def P5_3
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤
      (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
      NavierStokesMillennium.Spacetime
    ∧ ContDiffOn ℝ ⊤
        (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
        NavierStokesMillennium.Spacetime

/-- **P5.4** — solution pressure periodic on `ℝ³ × [0, ∞)`.

SOURCE: Fefferman 2001 erratum, p.5, propagated to the solution.
Applies to Routes B and D. -/
def P5_4 (p : NavierStokesMillennium.Space 3 → ℝ → ℝ) : Prop :=
  ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
    t ∈ NavierStokesMillennium.TimeDomain →
    ∀ (j : Fin 3), p (x + NavierStokesMillennium.e j) t = p x t

/-- **P5.5** — pressure normalised to zero mean over the period cube on `T³`.

The PDE-community zero-mean gauge convention, not in Fefferman's text.
Mathematically inert on `T³`: for any periodic-smooth `(u, p)` satisfying
the Navier–Stokes hypotheses, `(u, p − ⨍p)` satisfies the same hypotheses
with zero mean, since only `∇p` enters the momentum equation and the
mean-shift preserves smoothness, periodicity, and divergence-freeness.

SOURCE: PDE-community convention. Applies to Routes B and D. -/
def P5_5 (p : NavierStokesMillennium.Space 3 → ℝ → ℝ) : Prop :=
  ∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
    (∫ x in NavierStokesMillennium.unitCube, p x t ∂volume) = 0

/-- **P6.1** — uniform-in-time bounded kinetic energy.

SOURCE: Fefferman eq. (7), p.1 l.47–48:
"`∫_{R^n} |u(x,t)|^2 dx < C` for all `t ≥ 0`". Applies to Routes A and C. -/
def P6_1
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∃ (C : ℝ), ∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
    (∫ x : NavierStokesMillennium.Space 3, ‖u x t‖^2 ∂volume) < C

/-- **P7.1** — applied force vanishes identically (Route A specialization).

SOURCE: Fefferman p.2 l.16: "Take `f(x,t)` to be identically zero". -/
def P7_1
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  f_applied = fun (_ : NavierStokesMillennium.Space 3) (_ : ℝ) =>
    (0 : NavierStokesMillennium.Space 3)

/-- **P7.2** — applied force vanishes identically (Route B specialization).

SOURCE: Fefferman p.2 l.22: "we take `f(x,t)` to be identically zero". -/
def P7_2
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  f_applied = fun (_ : NavierStokesMillennium.Space 3) (_ : ℝ) =>
    (0 : NavierStokesMillennium.Space 3)

/-- **P8.1** — corrected weak Navier–Stokes identity.

SOURCE: Fefferman eq. (12) with the 2001 erratum applied (erratum p.5). -/
def P8_1 (ν : ℝ)
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
    (p : NavierStokesMillennium.Space 3 → ℝ → ℝ)
    (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  NavierStokesMillennium.NSWeakIdentity ν u p f_applied

/-- **P8.2** — test-function divergence identity (weak incompressibility).

SOURCE: Fefferman eq. (13), p.3 l.34–36. -/
def P8_2
    (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3) :
    Prop :=
  ∀ (φ : NavierStokesMillennium.Space 3 → ℝ → ℝ),
    ContDiff ℝ ⊤ (Function.uncurry φ) →
    HasCompactSupport (Function.uncurry φ) →
    (∫ (xt : NavierStokesMillennium.Space 3 × ℝ),
        inner ℝ (u xt.1 xt.2)
          (NavierStokesMillennium.gradientScalar (fun y => φ y xt.2) xt.1)) = 0

/- ### Quantifier-shape priors (route structure)

- **P9.A** — Route A: universal in `u₀`, existential in `(u, p)`
  (Fefferman p.2 l.13–17).
- **P9.B** — Route B: universal in `u₀`, existential in `(u, p)`
  (Fefferman p.2 l.18–24).
- **P9.C** — Route C: existential in `(u₀, f_applied)`, asserts
  non-existence of `(u, p)` (Fefferman p.2 l.25–31).
- **P9.D** — Route D: existential in `(u₀, f_applied)`, asserts
  non-existence of `(u, p)` (Fefferman p.2 l.32–37).
-/

/- ## Section 2 — Proofs

The four route assemblies of the Clay Navier–Stokes problem. The prize is
awarded for a proof of any one of the four. -/

/-- **Route A** — Existence and smoothness of Navier–Stokes on `ℝ³`.

SOURCE: Fefferman p.2 l.13–17. Claim: for any `ν > 0` and any Schwartz-class
divergence-free initial datum `u₀`, there exist `(u, p)` smooth on
`ℝ³ × [0, ∞)`, divergence-free, agreeing with `u₀` at `t = 0`, satisfying the
Navier–Stokes momentum equation with zero applied force, and with uniformly
bounded kinetic energy. -/
@[category research open, AMS 35 46 76]
theorem feff_A : ∀ (ν : ℝ),
    0 < ν →                                                              -- P1.2
    ∀ (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3),
    ContDiff ℝ ⊤ u₀ →                                                   -- P1.3
    (∀ x : NavierStokesMillennium.Space 3,
        NavierStokesMillennium.divergence u₀ x = 0) →                    -- P1.4
    (∀ (k K : ℕ), ∃ (C : ℝ), ∀ x : NavierStokesMillennium.Space 3,
        ‖iteratedFDeriv ℝ k u₀ x‖ ≤ C * (1 + ‖x‖)^(-(K : ℝ))) →         -- P3.1
    ∃ (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
      (p : NavierStokesMillennium.Space 3 → ℝ → ℝ),
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            NavierStokesMillennium.NSMomentumPt ν u p
              (fun _ _ => (0 : NavierStokesMillennium.Space 3)) x t) ∧ -- P2.1 with P7.1
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            NavierStokesMillennium.divergence (fun y => u y t) x = 0) ∧ -- P2.2
        (∀ x : NavierStokesMillennium.Space 3, u x 0 = u₀ x) ∧          -- P2.3
        (ContDiffOn ℝ ⊤
            (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
            NavierStokesMillennium.Spacetime ∧
          ContDiffOn ℝ ⊤
            (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
            NavierStokesMillennium.Spacetime) ∧                        -- P5.1
        (∃ (C : ℝ), ∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
            (∫ x : NavierStokesMillennium.Space 3, ‖u x t‖^2 ∂volume) < C) := by -- P6.1
  sorry

/-- **Route B** — Existence and smoothness of Navier–Stokes on `T³`.

SOURCE: Fefferman p.2 l.18–24. Claim: for any `ν > 0` and any smooth periodic
divergence-free initial datum `u₀`, there exist `(u, p)` smooth on
`T³ × [0, ∞)`, periodic, divergence-free, agreeing with `u₀` at `t = 0`,
satisfying the Navier–Stokes momentum equation with zero applied force and
the standard pressure gauge fixing on the torus. -/
@[category research open, AMS 35 46 76]
theorem feff_B : ∀ (ν : ℝ),
    0 < ν →                                                              -- P1.2
    ∀ (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3),
    ContDiff ℝ ⊤ u₀ →                                                   -- P1.3 (= P4.5)
    (∀ x : NavierStokesMillennium.Space 3,
        NavierStokesMillennium.divergence u₀ x = 0) →                    -- P1.4
    (∀ (x : NavierStokesMillennium.Space 3) (j : Fin 3),
        u₀ (x + NavierStokesMillennium.e j) = u₀ x) →                    -- P4.1
    ∃ (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
      (p : NavierStokesMillennium.Space 3 → ℝ → ℝ),
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            NavierStokesMillennium.NSMomentumPt ν u p
              (fun _ _ => (0 : NavierStokesMillennium.Space 3)) x t) ∧ -- P2.1 with P7.2
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            NavierStokesMillennium.divergence (fun y => u y t) x = 0) ∧ -- P2.2
        (∀ x : NavierStokesMillennium.Space 3, u x 0 = u₀ x) ∧          -- P2.3
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            ∀ (j : Fin 3), u (x + NavierStokesMillennium.e j) t = u x t) ∧ -- P5.2
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
            t ∈ NavierStokesMillennium.TimeDomain →
            ∀ (j : Fin 3), p (x + NavierStokesMillennium.e j) t = p x t) ∧ -- P5.4
        (∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
            (∫ x in NavierStokesMillennium.unitCube, p x t ∂volume) = 0) ∧ -- P5.5
        (ContDiffOn ℝ ⊤
            (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
            NavierStokesMillennium.Spacetime ∧
          ContDiffOn ℝ ⊤
            (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
            NavierStokesMillennium.Spacetime) := by                    -- P5.3
  sorry

/-- **Route C** — Breakdown of Navier–Stokes on `ℝ³` with nonzero applied force.

SOURCE: Fefferman p.2 l.25–31. Claim: there exist a Schwartz-class
divergence-free initial datum `u₀` and a smooth Schwartz-decaying applied
force `f_applied` such that the Navier–Stokes initial-value problem admits
no globally smooth solution with uniformly bounded kinetic energy. -/
@[category research open, AMS 35 46 76]
theorem feff_C : ∀ (ν : ℝ),
    0 < ν →                                                              -- P1.2
    ∃ (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3)
      (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3),
        ContDiff ℝ ⊤ u₀ ∧                                              -- P1.3
        (∀ x : NavierStokesMillennium.Space 3,
            NavierStokesMillennium.divergence u₀ x = 0) ∧                -- P1.4
        (∀ (k K : ℕ), ∃ (C : ℝ), ∀ x : NavierStokesMillennium.Space 3,
            ‖iteratedFDeriv ℝ k u₀ x‖ ≤ C * (1 + ‖x‖)^(-(K : ℝ))) ∧     -- P3.1
        ContDiffOn ℝ ⊤ (Function.uncurry f_applied)
          NavierStokesMillennium.Spacetime ∧                            -- P3.3
        (∀ (k m K : ℕ), ∃ (C : ℝ),
            ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
              t ∈ NavierStokesMillennium.TimeDomain →
              NavierStokesMillennium.spatiotemporalNorm k m f_applied x t
                ≤ C * (1 + ‖x‖ + t)^(-(K : ℝ))) ∧                       -- P3.2
        ¬ ∃ (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
          (p : NavierStokesMillennium.Space 3 → ℝ → ℝ),
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                NavierStokesMillennium.NSMomentumPt ν u p f_applied x t) ∧ -- P2.1
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                NavierStokesMillennium.divergence (fun y => u y t) x = 0) ∧ -- P2.2
            (∀ x : NavierStokesMillennium.Space 3, u x 0 = u₀ x) ∧      -- P2.3
            (ContDiffOn ℝ ⊤
                (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
                NavierStokesMillennium.Spacetime ∧
              ContDiffOn ℝ ⊤
                (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
                NavierStokesMillennium.Spacetime) ∧                    -- P5.1
            (∃ (C : ℝ), ∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
                (∫ x : NavierStokesMillennium.Space 3, ‖u x t‖^2 ∂volume) < C) := by -- P6.1
  sorry

/-- **Route D** — Breakdown of Navier–Stokes on `T³` with nonzero applied force.

SOURCE: Fefferman p.2 l.32–37. Claim: there exist a smooth periodic
divergence-free initial datum `u₀` and a smooth periodic time-decaying applied
force `f_applied` such that the Navier–Stokes initial-value problem on `T³`
admits no globally smooth periodic solution with the standard pressure gauge. -/
@[category research open, AMS 35 46 76]
theorem feff_D : ∀ (ν : ℝ),
    0 < ν →                                                              -- P1.2
    ∃ (u₀ : NavierStokesMillennium.Space 3 → NavierStokesMillennium.Space 3)
      (f_applied : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3),
        ContDiff ℝ ⊤ u₀ ∧                                              -- P1.3 (= P4.5)
        (∀ x : NavierStokesMillennium.Space 3,
            NavierStokesMillennium.divergence u₀ x = 0) ∧                -- P1.4
        (∀ (x : NavierStokesMillennium.Space 3) (j : Fin 3),
            u₀ (x + NavierStokesMillennium.e j) = u₀ x) ∧                -- P4.1
        ContDiffOn ℝ ⊤ (Function.uncurry f_applied)
          NavierStokesMillennium.Spacetime ∧                            -- P3.3
        (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ) (j : Fin 3),
            f_applied (x + NavierStokesMillennium.e j) t = f_applied x t) ∧ -- P4.2
        (∀ (k m K : ℕ), ∃ (C : ℝ),
            ∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
              t ∈ NavierStokesMillennium.TimeDomain →
              NavierStokesMillennium.spatiotemporalNorm k m f_applied x t
                ≤ C * (1 + t)^(-(K : ℝ))) ∧                             -- P4.4
        ¬ ∃ (u : NavierStokesMillennium.Space 3 → ℝ → NavierStokesMillennium.Space 3)
          (p : NavierStokesMillennium.Space 3 → ℝ → ℝ),
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                NavierStokesMillennium.NSMomentumPt ν u p f_applied x t) ∧ -- P2.1
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                NavierStokesMillennium.divergence (fun y => u y t) x = 0) ∧ -- P2.2
            (∀ x : NavierStokesMillennium.Space 3, u x 0 = u₀ x) ∧      -- P2.3
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                ∀ (j : Fin 3), u (x + NavierStokesMillennium.e j) t = u x t) ∧ -- P5.2
            (∀ (x : NavierStokesMillennium.Space 3) (t : ℝ),
                t ∈ NavierStokesMillennium.TimeDomain →
                ∀ (j : Fin 3), p (x + NavierStokesMillennium.e j) t = p x t) ∧ -- P5.4
            (∀ (t : ℝ), t ∈ NavierStokesMillennium.TimeDomain →
                (∫ x in NavierStokesMillennium.unitCube, p x t ∂volume) = 0) ∧ -- P5.5
            (ContDiffOn ℝ ⊤
                (fun xt : NavierStokesMillennium.Space 3 × ℝ => u xt.1 xt.2)
                NavierStokesMillennium.Spacetime ∧
              ContDiffOn ℝ ⊤
                (fun xt : NavierStokesMillennium.Space 3 × ℝ => p xt.1 xt.2)
                NavierStokesMillennium.Spacetime) := by                -- P5.3
  sorry

/- ## Section 3 — Results

The Clay Millennium Prize is awarded for a proof of any one of Routes A, B,
C, or D. -/

/-- **The Clay Millennium Prize for the Navier–Stokes Equation.**

Proved when any one of `feff_A`, `feff_B`, `feff_C`, `feff_D` is proved. -/
@[category research open, AMS 35 46 76]
theorem clay_millennium_prize_navier_stokes :
    type_of% NavierStokesMillennium.feff_A
      ∨ type_of% NavierStokesMillennium.feff_B
      ∨ type_of% NavierStokesMillennium.feff_C
      ∨ type_of% NavierStokesMillennium.feff_D := by
  sorry

end NavierStokesMillennium
