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
# Hilbert's Fifth Problem and the Hilbert–Smith Conjecture

The **Hilbert–Smith conjecture** states that a locally compact topological group acting
continuously and faithfully on a connected finite-dimensional topological manifold must be a
Lie group. It remains open in general; Pardon proved it for 3-manifolds in 2013.
An equivalent formulation: no p-adic integer group `ℤ_[p]` can act faithfully on any
connected finite-dimensional topological manifold.

## Main statements

- `hilbert_smith_conjecture`: the Hilbert–Smith conjecture.
- `hilbert_smith_padic_formulation`: the equivalent formulation for `ℤ_[p]`.
- `hilbert_smith_conjecture.variants.dimension_three`: Pardon's theorem for 3-manifolds.
- `hilbert_smith_conjecture.variants.riemannian`: the case of isometric actions on Riemannian
  manifolds.
- `hilbert_fifth_problem`: Hilbert's fifth problem, solved by Gleason, Montgomery and Zippin.

## Implementation notes

`AdmitsLieGroupStructure G`, defined in
`FormalConjecturesForMathlib.Geometry.Manifold.LieGroupPresentation`, says that `G` is
continuously isomorphic to a finite-dimensional real-analytic Lie group. Lie groups are Hausdorff
but not assumed second countable: every discrete group is a `0`-dimensional Lie group
(`admitsLieGroupStructure_of_discreteTopology`). This matters for the Hilbert–Smith conjecture,
since uncountable discrete groups act continuously and faithfully on connected manifolds, for
instance `ℝ` with the discrete topology acting on `ℝ` by translations.

The acting group is not assumed Hausdorff: a topological group acting continuously and
faithfully on a Hausdorff space is Hausdorff, because the closure of the identity acts trivially.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%E2%80%93Smith_conjecture)
- [Tao's blog](https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/)
- [Pardon 2013] J. Pardon, *The Hilbert–Smith conjecture for three-manifolds*,
  J. Amer. Math. Soc. 26 (2013), 879–899. https://doi.org/10.1090/S0894-0347-2013-00766-3,
  [arXiv:1112.2324](https://arxiv.org/abs/1112.2324)
- [Myers–Steenrod 1939] S. B. Myers, N. E. Steenrod, *The group of isometries of a Riemannian
  manifold*, Ann. of Math. 40 (1939), 400–416. https://doi.org/10.2307/1968928
- [van den Dries–Goldbring 2015] L. van den Dries, I. Goldbring, *Hilbert's 5th problem*,
  Enseign. Math. 61 (2015), 3–43. https://doi.org/10.4171/LEM/61-1/2-2
-/

namespace Hilbert5

open scoped Manifold ContDiff Bundle

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- The circle group admits a Lie group structure. -/
@[category test, AMS 22]
theorem admitsLieGroupStructure_circle : AdmitsLieGroupStructure Circle :=
  admitsLieGroupStructure_of_lieGroup (n := 1)

/-- The discrete group `ℤ` admits a Lie group structure. -/
@[category test, AMS 22]
theorem admitsLieGroupStructure_multiplicative_int :
    AdmitsLieGroupStructure (Multiplicative ℤ) :=
  admitsLieGroupStructure_of_discreteTopology

/-- **Hilbert–Smith conjecture**: every locally compact topological group acting continuously
and faithfully on a connected finite-dimensional topological manifold is a Lie group. -/
@[category research open, AMS 22 57 58]
theorem hilbert_smith_conjecture
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    AdmitsLieGroupStructure G := by
  sorry

/-- The Hilbert–Smith conjecture holds for actions by isometries of a connected smooth Riemannian
manifold `X`: the isometry group of `X` is a Lie group by the Myers–Steenrod theorem, so `G` has
no small subgroups and is a Lie group by the Gleason–Montgomery–Zippin theorem.

Here `X` carries its Riemannian distance (`IsRiemannianManifold`), so the metric topology of `X`
is its manifold topology. -/
@[category research solved, AMS 22 53 57 58]
theorem hilbert_smith_conjecture.variants.riemannian {X : Type*} [EMetricSpace X]
    [ConnectedSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) X]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X]
    (hiso : ∀ g : G, Isometry (g • · : X → X)) :
    AdmitsLieGroupStructure G := by
  sorry

/-- **Pardon's theorem** (2013): the Hilbert–Smith conjecture holds for connected 3-manifolds,
see [Pardon 2013]. -/
@[category research solved, AMS 22 57 58]
theorem hilbert_smith_conjecture.variants.dimension_three {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    AdmitsLieGroupStructure G := by
  sorry

/-- **p-adic formulation**: the p-adic integers `ℤ_[p]` cannot act continuously and faithfully
on a connected finite-dimensional topological manifold. This is equivalent to
`hilbert_smith_conjecture` by the Gleason–Yamabe theorem together with Newman's theorem on
periodic transformations of manifolds. -/
@[category research open, AMS 22 57 58]
theorem hilbert_smith_padic_formulation (p : ℕ) [Fact p.Prime]
    [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X := by
  sorry

/-- **Hilbert's fifth problem** (Gleason–Montgomery–Zippin, 1952): every Hausdorff,
second-countable topological group modeled on a finite-dimensional Euclidean space is continuously
isomorphic to a real-analytic Lie group.

The input `ChartedSpace` supplies only a topological atlas. The compatible analytic atlas and
analytic group operations belong to the output `LieGroupPresentation`. -/
@[category research solved, AMS 22 57]
theorem hilbert_fifth_problem
    [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    Nonempty (LieGroupPresentation G n) := by
  sorry

end Hilbert5
