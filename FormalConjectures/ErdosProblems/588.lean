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
# Erdős Problem 588

Is it true that the maximum number of k-rich lines determined by n points in the plane with no
k+1 collinear is o(n²) for all k ≥ 4? This generalises Problem #101 (the case k = 4).

Kárteszi [Ka63] proved f_k(n) ≫_k n log n for k ≥ 4. Grünbaum [Gr76] improved this to
f_k(n) ≫_k n^{1+1/(k-2)}. Solymosi and Stojaković [SoSt13] constructed point sets with
no (k+1) collinear and ≥ n^{2 - O_k(1/√(log n))} k-rich lines, showing the answer is close
to quadratic if false.

Erdős offered $100 for a resolution of this problem.

*Reference:* [erdosproblems.com/588](https://www.erdosproblems.com/588)

[Er84] Erdős, P., _Some old and new problems on combinatorial geometry_, 1984.

[BGS74] Burr, S. A., Grünbaum, B., and Sloane, N. J. A., _The orchard problem_.
Geometriae Dedicata (1974), 397–424.

[FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of
triangles_. Proc. Amer. Math. Soc. (1984), 561–566.

[Ka63] Kárteszi, F., _Sylvester egy tételéről és Erdős egy sejtéséről_.
Matematikai Lapok (1963), 3–10.

[Gr76] Grünbaum, B., _New views on some old questions of combinatorial geometry_.
Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451–468.

[SoSt13] Solymosi, J. and Stojaković, M., _Many collinear k-tuples with no k+1 collinear
points_. Discrete Comput. Geom. (2013), 811–820.
-/

namespace Erdos588

/--
A finite point set in $\mathbb{R}^2$ has no $(k+1)$ collinear points if every $(k+1)$-element
subset is not collinear (i.e., no line contains $k+1$ or more of the points).
-/
def NoKPlusOneCollinear (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = k + 1 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of $k$-rich lines: the number of distinct affine lines in $\mathbb{R}^2$ that
contain at least $k$ points from $P$.
-/
noncomputable def kRichLineCount (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Let $f_k(n)$ be the maximum number of lines containing at least $k$ points,
over all configurations of $n$ points in $\mathbb{R}^2$ with no $k+1$ collinear.
Is it true that $f_k(n) = o(n^2)$ for all $k \geq 4$?

This is a generalisation of Problem \#101 (the case $k = 4$). The restriction
to $k \geq 4$ is necessary since Sylvester showed $f_3(n) = n^2/6 + O(n)$.

Formally: for every $k \geq 4$ and every $\varepsilon > 0$, there exists $N$ such that for
all $n \geq N$ and every set $P$ of $n$ points in $\mathbb{R}^2$ with no $k+1$ collinear, the
count of $k$-rich lines is at most $\varepsilon \cdot n^2$.
-/
@[category research open, AMS 5 52]
theorem erdos_588 : answer(sorry) ↔
    ∀ k : ℕ, k ≥ 4 →
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
            P.card = n →
            NoKPlusOneCollinear k P →
            (kRichLineCount k P : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos588
