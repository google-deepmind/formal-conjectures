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
# Erdős Problem 769

*Reference:* [erdosproblems.com/769](https://www.erdosproblems.com/769)

Let $c(n)$ be minimal such that if $k \geq c(n)$ then the $n$-dimensional unit cube
can be decomposed into $k$ homothetic $n$-dimensional cubes. Is it true that
$c(n) \gg n^n$?

A problem first investigated by Hadwiger, who proved $c(n) \geq 2^n + 2^{n-1}$.

[Er74b] Burgess, D.A. and Erdős, P., on a problem in combinatorial geometry, 1974.

[CoMa18] Connor, S. and Marmorino, M., on cube decompositions, 2018.
-/

namespace Erdos769

/-- The unit cube $[0,1]^n$ in $\mathbb{R}^n$. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- An axis-aligned cube in $\mathbb{R}^n$ with given corner and side length. -/
def axisCube {n : ℕ} (corner : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, corner i ≤ x i ∧ x i ≤ corner i + s}

/-- The interior of an axis-aligned cube in $\mathbb{R}^n$. -/
def axisCubeInterior {n : ℕ} (corner : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, corner i < x i ∧ x i < corner i + s}

/-- The $n$-dimensional unit cube $[0,1]^n$ can be decomposed into exactly $k$
homothetic cubes (axis-aligned cubes with positive side lengths) such that
the cubes cover the unit cube and have pairwise disjoint interiors. -/
def CanDecomposeUnitCube (n k : ℕ) : Prop :=
  ∃ (corners : Fin k → Fin n → ℝ) (sides : Fin k → ℝ),
    (∀ j, sides j > 0) ∧
    (∀ j, axisCube (corners j) (sides j) ⊆ unitCube n) ∧
    (∀ x ∈ unitCube n, ∃ j, x ∈ axisCube (corners j) (sides j)) ∧
    (∀ i j, i ≠ j → ∀ x,
      ¬(x ∈ axisCubeInterior (corners i) (sides i) ∧
        x ∈ axisCubeInterior (corners j) (sides j)))

/--
Erdős Problem 769 [Er74b]:

Let $c(n)$ be minimal such that if $k \geq c(n)$ then the $n$-dimensional unit cube
can be decomposed into $k$ homothetic $n$-dimensional cubes. Is it true that
$c(n) \gg n^n$?

Formalized as: there exists $C > 0$ and $N_0$ such that for all $n \geq N_0$,
if every $k \geq m$ permits a decomposition of the unit $n$-cube into $k$ homothetic
cubes, then $m \geq C \cdot n^n$ (i.e., the threshold $c(n) \geq C \cdot n^n$).
-/
@[category research open, AMS 52]
theorem erdos_769 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ m : ℕ, (∀ k : ℕ, k ≥ m → CanDecomposeUnitCube n k) →
        (m : ℝ) ≥ C * (n : ℝ) ^ n := by
  sorry

end Erdos769
