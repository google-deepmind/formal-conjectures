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

[Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974), 197-202.

[CoMa18] Connor, P. and Marmorino, P., *Decomposing cubes into smaller cubes*. J. Geom.
(2018), Paper No. 19, 11.

[Hu98] Hudelson, M., *Dissecting d-cubes into smaller d-cubes*. J. Combin. Theory Ser. A
(1998), 190-200.
-/

namespace Erdos769

open Set

/-- The $n$-dimensional unit cube $[0,1]^n$ can be decomposed into exactly $k$
homothetic cubes (axis-aligned cubes with positive side lengths) such that
the cubes cover the unit cube and have pairwise disjoint interiors. -/
def CanDecomposeUnitCube (n k : ℕ) : Prop :=
  ∃ (corners : Fin k → Fin n → ℝ) (sides : Fin k → ℝ),
    (∀ j, sides j > 0) ∧
    (∀ j, pi univ (fun i => Icc (corners j i) (corners j i + sides j)) ⊆
      pi univ (fun _ => Icc 0 1)) ∧
    (∀ x ∈ pi univ (fun _ => Icc (0 : ℝ) 1), ∃ j,
      x ∈ pi univ (fun i => Icc (corners j i) (corners j i + sides j))) ∧
    (∀ i j, i ≠ j → ∀ x,
      ¬(x ∈ pi univ (fun l => Ioo (corners i l) (corners i l + sides i)) ∧
        x ∈ pi univ (fun l => Ioo (corners j l) (corners j l + sides j))))

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
