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
# Erdős Problem 130

*Reference:* [erdosproblems.com/130](https://www.erdosproblems.com/130)
-/

namespace Erdos130

open scoped Classical

/-- A point of the plane. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance. -/
def sqDist (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The three points `p, q, r` are collinear (vanishing signed area). -/
def Collinear (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- The four points `p, q, r, s` lie on a common circle: there is a centre `o`
equidistant from all four. -/
def Concyclic4 (p q r s : Point) : Prop :=
  ∃ o : Point, sqDist o p = sqDist o q ∧ sqDist o p = sqDist o r ∧ sqDist o p = sqDist o s

/-- General position: no three points collinear and no four points concyclic. -/
def GeneralPosition (A : Set Point) : Prop :=
  (∀ ⦃p q r⦄, p ∈ A → q ∈ A → r ∈ A →
      p ≠ q → p ≠ r → q ≠ r → ¬ Collinear p q r) ∧
  (∀ ⦃p q r s⦄, p ∈ A → q ∈ A → r ∈ A → s ∈ A →
      p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s → ¬ Concyclic4 p q r s)

/-- Two points are adjacent in the integer-distance graph iff they are distinct
and their distance is a positive integer (equivalently `sqDist` is a positive
perfect square). -/
def Adjacent (p q : Point) : Prop :=
  p ≠ q ∧ ∃ n : ℕ, 0 < n ∧ sqDist p q = (n : ℝ) ^ 2

/-- The integer-distance graph on `A` has a proper colouring with `k` colours. -/
def HasKColoring (A : Set Point) (k : ℕ) : Prop :=
  ∃ color : A → Fin k, ∀ x y : A, Adjacent x.1 y.1 → color x ≠ color y

/--
Let $A\subset\mathbb{R}^2$ be an infinite set which contains no three points on a
line and no four points on a circle. Consider the graph with vertices the points
in $A$, where two vertices are joined by an edge if and only if they are an
integer distance apart. How large can the chromatic number and clique number of
this graph be? In particular, can the chromatic number be infinite?

The chromatic number can be infinite: there is an infinite general-position set
whose integer-distance graph admits no finite proper colouring.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-130/Research/Basic.lean"]
theorem erdos_130 :
    answer(True) ↔
      ∃ A : Set Point, A.Infinite ∧ GeneralPosition A ∧ ∀ k : ℕ, ¬ HasKColoring A k := by
  sorry

end Erdos130
