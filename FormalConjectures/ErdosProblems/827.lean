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
# Erdős Problem 827

*References:*
- [erdosproblems.com/827](https://www.erdosproblems.com/827)
- [Er75h] Erdős, P., *Some problems on elementary geometry*. Austral. Math. Soc. Gaz. 2 (1975),
  2-3.
- [Er78c] Erdős, P., *Some more problems on elementary geometry*. Austral. Math. Soc. Gaz. 5
  (1978), 52-54.
- [MaRo15] Martínez, L. and Roldán-Pensado, E., *Points defining triangles with distinct
  circumradii*. Acta Math. Hungar. 145 (2015), 136-141.
  [arXiv:1402.6276](https://arxiv.org/abs/1402.6276)
-/

@[expose] public section

open Filter Asymptotics EuclideanGeometry

namespace Erdos827

/-- The points of `S` lie on a circle of radius `r`. -/
def OnCircleOfRadius (S : Finset ℝ²) (r : ℝ) : Prop :=
  ∃ c : ℝ², ∀ p ∈ S, dist p c = r

/-- Distinct triples of points of `S` never lie on circles of the same radius. For a set with no
three collinear points, every triple lies on exactly one circle, so this says that the
$\binom{|S|}{3}$ circumradii are pairwise different. -/
def HasDistinctCircumradii (S : Finset ℝ²) : Prop :=
  ∀ T ⊆ S, ∀ T' ⊆ S, T.card = 3 → T'.card = 3 → T ≠ T' →
    ∀ r : ℝ, OnCircleOfRadius T r → ¬ OnCircleOfRadius T' r

/-- $n_k$: the least $m$ such that every set of $m$ points of $\mathbb{R}^2$ in general position
(no three collinear, no four concyclic) contains $k$ points whose $\binom{k}{3}$ triples
determine circles of pairwise different radii. By [MaRo15] such an $m$ exists for every $k$, so
`sInf` is a true minimum. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ X : Finset ℝ², X.card = m → InGeneralPosition (X : Set ℝ²) →
    ∃ Y ⊆ X, Y.card = k ∧ HasDistinctCircumradii Y}

/-- If every set of `m` points in general position contains `k` points with pairwise different
circumradii, then $n_k \leq m$. -/
@[category API, AMS 52]
theorem n_le {k m : ℕ}
    (h : ∀ X : Finset ℝ², X.card = m → InGeneralPosition (X : Set ℝ²) →
      ∃ Y ⊆ X, Y.card = k ∧ HasDistinctCircumradii Y) :
    n k ≤ m :=
  Nat.sInf_le h

def erdos_827.answer : ℕ → ℕ := sorry

/--
Let $n_k$ be minimal such that if $n_k$ points in $\mathbb{R}^2$ are in general position then
there exists a subset of $k$ points such that all $\binom{k}{3}$ triples determine circles of
different radii.

Determine $n_k$.

General position means that no three points are collinear and no four are concyclic, as in
[Er75h] (quoted in [MaRo15]).
-/
@[category research open, question value, AMS 52]
theorem erdos_827 : n = erdos_827.answer := by
  sorry

/--
In [Er78c] Erdős gave an argument for $n_k \leq k+2\binom{k-1}{2}\binom{k-1}{3}$, but this
argument is incorrect, as explained by Martínez and Roldán-Pensado [MaRo15], who give a corrected
argument that proves $n_k\ll k^9$.

[MaRo15, Theorem 1.1] assumes only that no four points lie on a line or a circle. That class
contains the sets in general position, so the bound holds for $n_k$ as defined here.
-/
@[category research solved, AMS 52]
theorem erdos_827.variants.martinez_roldan_pensado :
    (fun k : ℕ ↦ (n k : ℝ)) =O[atTop] fun k : ℕ ↦ (k : ℝ) ^ 9 := by
  sorry

/--
Martínez and Roldán-Pensado [MaRo15, Theorem 1.2] show that $n_4 \leq 9$.
-/
@[category research solved, AMS 52]
theorem erdos_827.variants.n_four_le : n 4 ≤ 9 := by
  sorry

/--
Martínez and Roldán-Pensado [MaRo15, Theorem 1.2] show that $n_5 \leq 37$.
-/
@[category research solved, AMS 52]
theorem erdos_827.variants.n_five_le : n 5 ≤ 37 := by
  sorry

end Erdos827
