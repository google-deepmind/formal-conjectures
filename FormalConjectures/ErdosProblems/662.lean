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
# Erdős Problem 662

*Reference:* [erdosproblems.com/662](https://www.erdosproblems.com/662)

Consider the triangular lattice with minimal distance between two points $1$.
Denote by $f(t)$ the number of lattice points within distance $t$ of any fixed
lattice point. For example $f(1) = 6$, $f(\sqrt{3}) = 12$.

Let $x_1, \ldots, x_n \in \mathbb{R}^2$ be such that $d(x_i, x_j) \geq 1$ for
all $i \neq j$. Is it true that, provided $n$ is sufficiently large depending on
$t$, the number of ordered pairs $(i, j)$ with $i \neq j$ and $d(x_i, x_j) \leq t$
is at most $n \cdot f(t)$?

Note: The original problem statement in [Er97e] contains apparent typos and is
acknowledged as ambiguous. This formalization captures what appears to be the
most natural interpretation: among unit-separated point sets, the triangular
lattice maximizes the number of close pairs.

A problem of Erdős, Lovász, and Vesztergombi.
-/

open Classical

namespace Erdos662

/-- $f(t)$ is the number of integer pairs $(a, b) \neq (0, 0)$ with
$a^2 + ab + b^2 \leq t^2$, which equals the number of neighbors within distance
$t$ of any point in the triangular lattice (with unit minimal distance). The
squared distance from the origin to lattice point $(a, b)$ in the triangular
lattice is $a^2 + ab + b^2$. -/
noncomputable def triangularLatticeNeighborCount (t : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | p ≠ (0, 0) ∧
    ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2) ≤ t ^ 2}

/-- The number of ordered pairs of distinct points in $P$ with distance at most $t$. -/
noncomputable def closePairCount
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (t : ℝ) : ℕ :=
  ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 ≤ t)).card

/--
**Erdős Problem 662** [Er97e, p.532]:

Among $n$ points in $\mathbb{R}^2$ with minimum pairwise distance $\geq 1$, is
the number of ordered pairs at distance $\leq t$ at most $n \cdot f(t)$, where
$f(t)$ is the number of neighbors within distance $t$ in the triangular lattice?
-/
@[category research open, AMS 52]
theorem erdos_662 : answer(sorry) ↔
    ∀ t : ℝ, t > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          (∀ p ∈ P, ∀ q ∈ P, p ≠ q → dist p q ≥ 1) →
          closePairCount P t ≤ n * triangularLatticeNeighborCount t := by
  sorry

end Erdos662
