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
# Sharp light sources characterization of ellipsoids by flat shadow boundaries

*Reference:* [arxiv/2603.29130](https://arxiv.org/abs/2603.29130)
**On flat shadow boundaries from point light sources and the characterization of ellipsoids**
by *Bartłomiej Zawalski*

A point light source $u \notin K$ illuminates a convex body $K \subset \mathbb{R}^n$ and creates
a **shadow boundary**: the set of points $x \in \partial K$ where the ray from $u$ through $x$ is
tangent to $K$. The shadow boundary is **flat** if it lies in an affine hyperplane.

The main theorem of the paper (with $n+2$ sources, $n \geq 4$) and a classical result due to
Blaschke (parallel light / directions at infinity) both conclude that if every boundary point
admits sufficiently many light sources in general position on its tangent hyperplane creating flat
shadow boundaries, then $K$ is an ellipsoid.

The sharp conjecture asks whether $n+1$ light sources already suffice (replacing $n+2$).
The $\ell_p^n$ ball ($p \neq 2$) shows $n$ sources are not enough.
-/

open Set Metric

namespace Arxiv.«2603.29130»

variable {n : ℕ}

/-- A **convex body** in $\mathbb{R}^n$: a compact convex set with nonempty interior. -/
def IsConvexBody (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The **shadow boundary** of $K$ with respect to a point light source $u \notin K$: the set of
boundary points $x \in \partial K$ such that the ray from $u$ through $x$ is tangent to $K$ at
$x$, i.e., every point of the ray beyond $x$ lies outside $K$. -/
def ShadowBoundary (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x ∈ frontier K | ∀ t : ℝ, 1 < t → u + t • (x - u) ∉ interior K}

/-- The shadow boundary from $u$ is **flat** if it is contained in some affine hyperplane,
i.e., there exist a nonzero vector $v$ and a constant $c$ such that
$\langle v, x \rangle = c$ for all $x$ in the shadow boundary. -/
def HasFlatShadowBoundary (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (v : EuclideanSpace ℝ (Fin n)) (_ : v ≠ 0) (c : ℝ),
    ShadowBoundary K u ⊆ {x | ⟪v, x⟫_ℝ = c}

/-- The **tangent hyperplane** at a smooth boundary point $p \in \partial K$ with outward unit
normal $\nu$: the affine hyperplane $\{x \mid \langle \nu, x\rangle = \langle \nu, p\rangle\}$. -/
def TangentHyperplane (p ν : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪ν, x⟫_ℝ = ⟪ν, p⟫_ℝ}

/-- A finite set $S$ of points is in **general linear position with respect to $p$** if no $n$
points of $S$ lie in a common affine hyperplane passing through $p$. More precisely: for every
$(n-1)$-element subset $T \subseteq S$, the affine span of $T$ does not contain $p$ unless it
spans a hyperplane that already contains all of $T$ — equivalently, no $n$ points of $S$ are
coplanar on a hyperplane through $p$. -/
def GeneralPositionWrt (p : EuclideanSpace ℝ (Fin n))
    (S : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ T : Finset (EuclideanSpace ℝ (Fin n)), T ⊆ S → T.card = n →
    ∀ (v : EuclideanSpace ℝ (Fin n)) (_ : v ≠ 0) (c : ℝ),
      ⟪v, p⟫_ℝ = c →
        ¬ (∀ x ∈ T, ⟪v, x⟫_ℝ = c)

/-- $K$ is an **ellipsoid**: the image of the closed unit ball under an invertible affine map.
Equivalently, $K = \{x \mid \langle A(x - c), x - c\rangle \leq 1\}$ for some centre
$c \in \mathbb{R}^n$ and some invertible symmetric positive-definite linear map $A$. -/
def IsEllipsoid (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (_ : Function.Bijective A),
    K = {x | ⟪A (x - c), x - c⟫_ℝ ≤ 1}

/--
**Conjecture (Zawalski, 2026).** Let $K \subset \mathbb{R}^n$, $n \geq 3$, be a convex body
with $C^3$ boundary. Suppose that for every boundary point $p \in \partial K$, there exist at
least $n+1$ point light sources on the tangent hyperplane $T_p \partial K$ in general linear
position with respect to $p$, each creating a flat shadow boundary on $K$. Then $K$ is an
ellipsoid.

The paper proves this with $n+2$ sources (for $n \geq 4$) in the main theorem, and the
$\ell_p^n$ ball ($p > 1$, $p \neq 2$) witnesses that $n$ sources are not sufficient.
The sharp minimal number $n+1$ is left open as this conjecture.
-/
@[category research open, AMS 52 53]
theorem ellipsoid_of_flat_shadow_boundaries (hn : 3 ≤ n) :
    answer(sorry) ↔
    ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
      IsConvexBody K →
      (∀ p ∈ frontier K,
        ∃ (ν : EuclideanSpace ℝ (Fin n)) (_ : ν ≠ 0)
          (S : Finset (EuclideanSpace ℝ (Fin n))),
          n + 1 ≤ S.card ∧
          (∀ u ∈ S, u ∈ TangentHyperplane p ν) ∧
          GeneralPositionWrt p S ∧
          ∀ u ∈ S, HasFlatShadowBoundary K u) →
      IsEllipsoid K := by
  sorry

/--
**Theorem (Zawalski, 2026).** For $n \geq 4$, if every boundary point of a convex body $K$ with
$C^3$ boundary admits at least $n+2$ point light sources on its tangent hyperplane in general
linear position creating flat shadow boundaries, then $K$ is an ellipsoid.

This is the main result of the paper (Theorem 1 / Section 3). The conjecture above asks whether
$n+1$ sources already suffice.
-/
@[category research solved, AMS 52 53]
theorem ellipsoid_of_flat_shadow_boundaries_n_plus_two (hn4 : 4 ≤ n) :
    ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
      IsConvexBody K →
      (∀ p ∈ frontier K,
        ∃ (ν : EuclideanSpace ℝ (Fin n)) (_ : ν ≠ 0)
          (S : Finset (EuclideanSpace ℝ (Fin n))),
          n + 2 ≤ S.card ∧
          (∀ u ∈ S, u ∈ TangentHyperplane p ν) ∧
          GeneralPositionWrt p S ∧
          ∀ u ∈ S, HasFlatShadowBoundary K u) →
      IsEllipsoid K := by
  sorry

/--
**Theorem (Zawalski, 2026) — $n$ sources are insufficient.** The unit ball of $\ell_p^n$
($p > 1$, $p \neq 2$) is a convex body that is not an ellipsoid yet admits $n$ light sources in
general position on each tangent hyperplane creating flat shadow boundaries. This shows the sharp
threshold must be strictly greater than $n$.
-/
@[category research solved, AMS 52 46]
theorem n_sources_insufficient (hn : 3 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))),
      IsConvexBody K ∧ ¬IsEllipsoid K ∧
      ∀ p ∈ frontier K,
        ∃ (ν : EuclideanSpace ℝ (Fin n)) (_ : ν ≠ 0)
          (S : Finset (EuclideanSpace ℝ (Fin n))),
          n ≤ S.card ∧
          (∀ u ∈ S, u ∈ TangentHyperplane p ν) ∧
          GeneralPositionWrt p S ∧
          ∀ u ∈ S, HasFlatShadowBoundary K u := by
  sorry

end Arxiv.«2603.29130»
