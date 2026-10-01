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

public import FormalConjecturesUtil

/-!
# Erdős Problem 216

*References:*
- [erdosproblems.com/216](https://www.erdosproblems.com/216)
- [Ha78] Harborth, Heiko, *Konvexe Fünfecke in ebenen Punktmengen*. Elem. Math. (1978), 116--118.
- [Ho83] Horton, J. D., *Sets with no empty convex $7$-gons*. Canad. Math. Bull. (1983), 482--484.
- [Ni07] Nicolás, Carlos M., *The empty hexagon theorem*. Discrete Comput. Geom. (2007), 389--397.
- [Ge08] Gerken, Tobias, *Empty convex hexagons in planar point sets*. Discrete Comput. Geom. (2008),
  239--272.
- [HeSc24] Heule, Marijn J. H. and Scheucher, Manfred, *Happy Ending: An Empty Hexagon in Every Set
  of $30$ Points*. (2024).
-/

@[expose] public section

open EuclideanGeometry

namespace Erdos216

/-- The set `P` contains an empty convex `n`-gon: `n` points of `P` in convex position
whose convex hull has no point of `P` in its interior. -/
def HasEmptyConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep (S : Set ℝ²) ∧
    ∀ p ∈ P, p ∉ interior (convexHull ℝ (S : Set ℝ²))

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain an empty convex $k$-gon. -/
def cardSet (k : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyConvexNGon k pts }

/-- The function $g(k)$ specified in `erdos_216`, when the infimum is taken in `ℕ`.
This is a genuine Ramsey number only when `cardSet k` is nonempty; otherwise
`g k = 0` by the convention `sInf ∅ = 0`. -/
noncomputable def g (k : ℕ) : ℕ :=
  sInf (cardSet k)

/--
Let $g(k)$ be the smallest integer (if any such exists) such that any $g(k)$ points in
$\mathbb{R}^2$ contains an empty convex $k$-gon (i.e. with no point in the interior).
Does $g(k)$ exist? If so, estimate $g(k)$.

A variant of the 'happy ending' problem [107], which asks for the same without the 'no point in
the interior' restriction. Erdős observed $g(4)=5$ (as with the happy ending problem) but Harborth
[Ha78] showed $g(5)=10$. Nicolás [Ni07] and Gerken [Ge08] independently showed that $g(6)$ exists.
Horton [Ho83] showed that $g(n)$ does not exist for $n\geq 7$.

Heule and Scheucher [HeSc24] have proved that $g(6)=30$.

This problem is #2 in Ramsey Theory in the graphs problem collection.
-/
@[category research solved, AMS 52]
theorem erdos_216 : (∀ k ≥ 3, (cardSet k).Nonempty) ↔ answer(False) := by
  sorry

/-- The empty set is an empty convex $0$-gon. -/
@[category test, AMS 52]
theorem empty_zero (P : Set ℝ²) : HasEmptyConvexNGon 0 P := by
  refine ⟨∅, by simp, by simp, ?_, ?_⟩
  · intro a ha
    exact ha.elim
  · intro p hp
    simp [convexHull_empty]

/-- Erdős observed $g(4)=5$ (as with the happy ending problem). -/
@[category research solved, AMS 52]
theorem erdos_216.variants.g4 : (cardSet 4).Nonempty ∧ g 4 = 5 := by
  sorry

/-- Harborth [Ha78] showed $g(5)=10$. -/
@[category research solved, AMS 52]
theorem erdos_216.variants.g5 : (cardSet 5).Nonempty ∧ g 5 = 10 := by
  sorry

/-- Nicolás [Ni07] and Gerken [Ge08] independently showed that $g(6)$ exists. -/
@[category research solved, AMS 52]
theorem erdos_216.variants.g6_exists : (cardSet 6).Nonempty := by
  sorry

/-- Heule and Scheucher [HeSc24] have proved that $g(6)=30$. -/
@[category research solved, AMS 52]
theorem erdos_216.variants.g6 : g 6 = 30 := by
  sorry

/-- Horton [Ho83] showed that $g(n)$ does not exist for $n\geq 7$. -/
@[category research solved, AMS 52]
theorem erdos_216.variants.horton : ∀ n ≥ 7, cardSet n = ∅ := by
  sorry

end Erdos216
