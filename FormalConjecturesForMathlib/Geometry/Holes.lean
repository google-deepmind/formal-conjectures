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

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# `k`-holes in Euclidean space (dimension-generic)

This file collects the dimension-generic definitions of *convex position*,
*empty convex polytopes* and *`k`-holes* of finite point sets in `d`-dimensional
Euclidean space `ℝ^d`. They are used both for the plane (`d = 2`, see
`FormalConjecturesForMathlib.Geometry.2d`) and for higher dimensions (e.g.
`d = 3`, see `FormalConjectures.Arxiv.2105.08406.HigherDimHoles`).

A `k`-gon is a set of `k` points in *convex position* (`ConvexPos`), meaning no
point lies in the convex hull of the others. A `k`-hole is a `k`-gon whose convex
hull contains no other point of the set (`IsHoleIn`). A finite point set is in
*general position* in `ℝ^d` (`InGenPos`) if no `d + 1` of its points lie on a
common hyperplane, encoded by requiring every `(d + 1)`-subset to be affinely
independent.
-/

open scoped Finset

namespace EuclideanGeometry

/-- `ℝ^d`, `d`-dimensional Euclidean space. -/
abbrev EDim (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A set `S` in `ℝ^d` is in **convex position** (convex independent): no point of
`S` lies in the convex hull of the remaining points. Also known as a
"convex-independent set"; the point set encloses a convex shape. -/
def ConvexPos {d : ℕ} (S : Set (EDim d)) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- `EmptyIn S P` means that `S` carves out an *empty* shape inside `P`: no point
of `P` outside `S` lies in the convex hull of `S`. -/
def EmptyIn {d : ℕ} (S P : Set (EDim d)) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

/-- `IsHoleIn S P` means that `S` is a **hole** of `P`: the points of `S` are in
convex position, and no point of `P` outside `S` lies in the convex hull of `S`
(the hole is *empty*). `S` is the vertex set of a convex polytope whose convex
hull contains no other point of `P`. -/
def IsHoleIn {d : ℕ} (S P : Set (EDim d)) : Prop :=
  ConvexPos S ∧ EmptyIn S P

/-- `HasKHole k P` means the point set `P ⊆ ℝ^d` contains a **`k`-hole**: a
`k`-element subset in convex position whose convex hull contains no other point
of `P`. -/
def HasKHole {d : ℕ} (k : ℕ) (P : Set (EDim d)) : Prop :=
  ∃ S : Finset (EDim d), S.card = k ∧ ↑S ⊆ P ∧ IsHoleIn ↑S P

/-- A finite point set `P` in `ℝ^d` is in **general position** if no `d + 1` of
its points lie on a common hyperplane, encoded by requiring every `(d + 1)`-point
subset to be affinely independent. -/
def InGenPos {d : ℕ} (P : Finset (EDim d)) : Prop :=
  ∀ T : Finset (EDim d), T ⊆ P → T.card = d + 1 →
    AffineIndependent ℝ (fun x : (T : Set (EDim d)) => (x : EDim d))

end EuclideanGeometry
