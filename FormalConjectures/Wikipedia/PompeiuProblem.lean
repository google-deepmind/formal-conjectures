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

import FormalConjecturesUtil

/-!
# The Pompeiu problem

Let $\Omega \subset \mathbb{R}^{N+1}$ be a bounded domain. A **rigid motion** is an isometry of
$\mathbb{R}^{N+1}$ (a composition of translations and rotations), modelled here by an
`AffineIsometryEquiv` of Euclidean space with itself.

The domain $\Omega$ has the **Pompeiu property** if the only continuous function
$f : \mathbb{R}^{N+1} \to \mathbb{R}$ with $\int_{\sigma(\Omega)} f = 0$ for every rigid motion
$\sigma$ is $f \equiv 0$.

The **Pompeiu problem** (Pompeiu's conjecture) asserted that, among bounded simply connected
domains with Lipschitz boundary, the Euclidean ball is the *only* domain that **fails** to have
the Pompeiu property. That a ball fails is classical: radial functions built from Bessel
functions have vanishing integral over every congruent ball. The converse is false. Two
independent proofs of this negative conclusion are referenced below.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Pompeiu_problem)
- [Encyclopedia of Mathematics](https://encyclopediaofmath.org/wiki/Pompeiu_problem)
- [BST73] Brown, L., Schreiber, B. M. and Taylor, B. A., *Spectral synthesis and the Pompeiu
  problem*, Ann. Inst. Fourier 23 (1973), 125–154. (Proves a ball fails the Pompeiu property;
  for a ball of radius `R` the witness is `f(x) = sin(a x₁)` with `J_{n/2}(a R) = 0`.)
- Zalcman, L., *A bibliographic survey of the Pompeiu problem*, in Approximation by
  Solutions of Partial Differential Equations, NATO ASI Ser. 365 (1992), 185–194.
- [CLD26] [Cao-Labora, G. and de Dios Pont, J., *Schiffer*](https://github.com/jaumededios/Schiffer),
  a Lean 4 formalization of a non-disk planar counterexample.
- [CS26] Colbrook, M. J. and Stepaniants, G., *A computer-assisted counterexample to the planar
  Pompeiu and Schiffer conjectures*, [arXiv:2608.01579](https://arxiv.org/abs/2608.01579) (2026).
-/

open MeasureTheory Metric Topology

namespace PompeiuProblem

variable {N : ℕ}

/-- A **rigid motion** of $\mathbb{R}^{N+1}$: an affine isometry of Euclidean space onto itself
(a composition of translations and rotations/reflections). -/
abbrev RigidMotion (N : ℕ) :=
  AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin (N + 1))) (EuclideanSpace ℝ (Fin (N + 1)))

/-- A set `Ω` has the **Pompeiu property** if the only continuous `f : ℝ^{N+1} → ℝ` whose integral
over every rigid-motion image `σ(Ω)` vanishes is the zero function. -/
def HasPompeiuProperty (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin (N + 1)) → ℝ, Continuous f →
    (∀ σ : RigidMotion N, (∫ x in Set.image σ Ω, f x) = 0) → ∀ x, f x = 0

/-- `Ω` is a **Euclidean ball**: an open metric ball of positive radius. -/
def IsBall (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin (N + 1))) (r : ℝ), 0 < r ∧ Ω = Metric.ball c r

/-- `Ω` has **Lipschitz boundary** if every boundary point `p` has a neighbourhood `U` in which,
after some rigid motion `σ` (used to choose a "vertical" axis), `Ω` coincides with the strict
subgraph of a Lipschitz function `g` of the first `N` coordinates: a point `x ∈ U` lies in `Ω`
iff its last coordinate (in the `σ`-frame) is below `g` applied to its first `N` coordinates.
This is the standard definition of a Lipschitz domain. -/
def HasLipschitzBoundary (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))) : Prop :=
  ∀ p ∈ frontier Ω, ∃ (U : Set (EuclideanSpace ℝ (Fin (N + 1)))),
    U ∈ 𝓝 p ∧ ∃ (σ : RigidMotion N) (K : NNReal) (g : EuclideanSpace ℝ (Fin N) → ℝ),
      LipschitzWith K g ∧
        ∀ x ∈ U, x ∈ Ω ↔ (σ x) (Fin.last N) <
          g ((WithLp.equiv 2 (Fin N → ℝ)).symm (fun i : Fin N => (σ x) i.castSucc))

/-- The domain hypotheses of Pompeiu's problem: `Ω` is bounded, open, connected (a "domain"),
simply connected, and has Lipschitz boundary. -/
structure IsAdmissibleDomain (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))) : Prop where
  bounded            : Bornology.IsBounded Ω
  isOpen             : IsOpen Ω
  connected          : IsConnected Ω
  simplyConnected    : SimplyConnectedSpace Ω
  lipschitzBoundary  : HasLipschitzBoundary Ω

/--
**Pompeiu's conjecture is false.** There is a bounded, simply connected Lipschitz domain in
$\mathbb{R}^2$ which fails to have the Pompeiu property but is not a Euclidean ball. This conclusion
has two independent proofs: the Lean-formalized construction of Cao-Labora and de Dios Pont
[CLD26], and the computer-assisted construction of Colbrook and Stepaniants [CS26].
-/
@[category research solved, AMS 42,
  formal_proof using lean4 at
    "https://github.com/jaumededios/Schiffer/blob/2938e277969c329caf154e48a3d8823f3635c7f1/Schiffer/FormalConjecturesSolution.lean#L446-L469"]
theorem pompeiu_conjecture :
    ¬ ∀ (N : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))),
      IsAdmissibleDomain Ω → (¬ HasPompeiuProperty Ω ↔ IsBall Ω) := by
  sorry

/--
The classical (easy) direction, proved by Brown–Schreiber–Taylor [BST73]: a Euclidean ball fails
to have the Pompeiu property. For a ball of radius `R`, an explicit witness is `f(x) = sin(a x₁)`
where `a > 0` is chosen so that the Bessel function `J_{n/2}(a R) = 0`; its integral over every
congruent ball vanishes.
-/
@[category research solved, AMS 42]
theorem ball_not_hasPompeiuProperty (Ω : Set (EuclideanSpace ℝ (Fin (N + 1))))
    (hball : IsBall Ω) :
    ¬ HasPompeiuProperty Ω := by
  sorry

/--
The hard direction of the Pompeiu problem is false: some admissible planar domain lacks the
Pompeiu property without being a ball. Two independent proofs are given in [CLD26] and [CS26].
-/
@[category research solved, AMS 42,
  formal_proof using lean4 at
    "https://github.com/jaumededios/Schiffer/blob/2938e277969c329caf154e48a3d8823f3635c7f1/Schiffer/FormalConjecturesSolution.lean#L446-L469"]
theorem not_hasPompeiuProperty_imp_ball :
    ¬ ∀ (N : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))),
      IsAdmissibleDomain Ω → ¬ HasPompeiuProperty Ω → IsBall Ω := by
  sorry

/-- Sanity check: the zero function always integrates to `0` over every rigid-motion image, so the
hypothesis in `HasPompeiuProperty` is satisfiable (the property is not vacuously false). -/
@[category test, AMS 42]
theorem integral_zero_eq_zero (Ω : Set (EuclideanSpace ℝ (Fin (N + 1)))) (σ : RigidMotion N) :
    (∫ _x in Set.image σ Ω, (0 : ℝ)) = 0 := by
  simp

end PompeiuProblem
