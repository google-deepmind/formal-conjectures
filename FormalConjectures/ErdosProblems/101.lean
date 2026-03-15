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
# Erdős Problem 101

*Reference:* [erdosproblems.com/101](https://www.erdosproblems.com/101)

Given $n$ points in $\mathbb{R}^2$ with no five collinear, the number of lines containing at
least four of the points is $o(n^2)$. This carries a \$100 prize.

Under the no-five-collinear hypothesis, "at least four" and "exactly four" are equivalent,
since no line can contain five or more points.

Grünbaum [Gr76] constructed examples with $\gg n^{3/2}$ four-rich lines (no five collinear),
leading Erdős to initially guess $n^{3/2}$ as the correct order. Solymosi and Stojaković
[SoSt13] constructed point sets with no five collinear and $\geq n^{2 - O(1/\sqrt{\log n})}$
lines containing exactly four points, disproving Erdős's guess and showing the bound is
essentially tight.

This is a special case of Problem #588 (with $k = 4$). See also Problem #102 and Problem #669.

OEIS: [A006065](https://oeis.org/A006065).

[BGS74] Burr, S. A., Grünbaum, B., and Sloane, N. J. A., _The orchard problem_.
Geometriae Dedicata (1974), 397–424.

[FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of
triangles_. Proc. Amer. Math. Soc. (1984), 561–566.

[Gr76] Grünbaum, B., _New views on some old questions of combinatorial geometry_.
Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451–468.

[SoSt13] Solymosi, J. and Stojaković, M., _Many collinear k-tuples with no k+1 collinear
points_. Discrete Comput. Geom. (2013), 811–820.

[Er84] Erdős, P., _Some old and new problems on combinatorial geometry_, 1984.

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry
(Siófok, 1985), 167–177.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44–48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.
-/

namespace Erdos101

/--
A finite point set in $\mathbb{R}^2$ has no five collinear points if every five-element subset
is not collinear (i.e., no line contains five or more of the points).
-/
def NoFiveCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 5 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of $4$-rich lines: the number of distinct affine lines in $\mathbb{R}^2$ that
contain at least four points from $P$.

An affine line is a $1$-dimensional affine subspace (`Module.finrank` of its
direction submodule equals $1$).
-/
noncomputable def fourRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #101: Given $n$ points in $\mathbb{R}^2$, no five of which are collinear,
the number of lines containing at least four of the points is $o(n^2)$.

Formally: for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ and every
set $P$ of $n$ points in $\mathbb{R}^2$ with no five collinear, the count of $4$-rich lines
is at most $\varepsilon \cdot n^2$.
-/
@[category research open, AMS 5 52]
theorem erdos_101 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          NoFiveCollinear P →
          (fourRichLineCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos101
