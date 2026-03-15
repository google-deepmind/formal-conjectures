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
# Erdős Problem 960

For a set of $n$ points in $\mathbb{R}^2$ with no $k$ collinear, let $f_{r,k}(n)$ be the
minimum number of ordinary lines that guarantees the existence of $r$ points whose
$\binom{r}{2}$ determined lines are all ordinary. Erdős asked whether $f_{r,k}(n) = o(n^2)$
for fixed $r, k \geq 2$, and more strongly whether $f_{r,k}(n) = O(n)$.

*Reference:* [erdosproblems.com/960](https://www.erdosproblems.com/960)

[Er84] Erdős, P., _Some old and new problems on combinatorial geometry_, 1984.

See also: [Erdős Problem 209](https://www.erdosproblems.com/209).
-/

namespace Erdos960

/--
A finite point set in $\mathbb{R}^2$ has no $k$ collinear if every $k$-element subset
is not collinear (i.e., no line contains $k$ or more of the points).
-/
def NoKCollinear (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = k → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
An ordinary line of a point set $P$ is a line (1-dimensional affine subspace)
that contains exactly two points of $P$.
-/
def IsOrdinaryLine (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ L.direction = 1 ∧
  Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} = 2

/--
The number of ordinary lines determined by a point set $P$: the number of
lines (1-dimensional affine subspaces) containing exactly two points of $P$.
-/
noncomputable def ordinaryLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) | IsOrdinaryLine P L}

/--
The line through two distinct points in $\mathbb{R}^2$: the affine span of $\{p, q\}$.
-/
noncomputable def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ {p, q}

/--
A subset $A' \subseteq A$ of $r$ points has all its determined lines ordinary with
respect to $A$: for every pair of distinct points $p, q \in A'$, the line through
$p$ and $q$ is ordinary (contains exactly two points of $A$).
-/
def AllPairsOrdinary (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (A' : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A' ⊆ A ∧
  ∀ p ∈ A', ∀ q ∈ A', p ≠ q → IsOrdinaryLine A (lineThrough p q)

/--
$f_{r,k}(n)$: the minimum number of ordinary lines that guarantees the existence
of $r$ points, all of whose $\binom{r}{2}$ determined lines are ordinary.

More precisely, $f_{r,k}(n)$ is the smallest $m$ such that for every set $A$ of $n$
points in $\mathbb{R}^2$ with no $k$ collinear and at least $m$ ordinary lines, there exists
$A' \subseteq A$ with $|A'| = r$ such that every line determined by $A'$ is ordinary.
-/
noncomputable def fRk (r k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n →
    NoKCollinear k A →
    ordinaryLineCount A ≥ m →
    ∃ A' : Finset (EuclideanSpace ℝ (Fin 2)),
      A'.card = r ∧ AllPairsOrdinary A A'}

/--
Erdős Problem 960 [Er84]:

For fixed $r, k \geq 2$, the threshold $f_{r,k}(n)$ is $o(n^2)$. That is, for every
$\varepsilon > 0$ there exists $N$ such that for all $n \geq N$,
$f_{r,k}(n) \leq \varepsilon \cdot n^2$.

This is the weaker form of the conjecture. Erdős also asks whether perhaps
$f_{r,k}(n) \ll n$ (i.e., $f_{r,k}(n) = O(n)$).
-/
@[category research open, AMS 5 51]
theorem erdos_960 (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (fRk r k n : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 960, stronger form [Er84]:

For fixed $r, k \geq 2$, the threshold $f_{r,k}(n) = O(n)$. That is, there exists
$C > 0$ such that $f_{r,k}(n) \leq C \cdot n$ for all $n$.
-/
@[category research open, AMS 5 51]
theorem erdos_960.variants.strong (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, (fRk r k n : ℝ) ≤ C * (n : ℝ) := by
  sorry

end Erdos960
