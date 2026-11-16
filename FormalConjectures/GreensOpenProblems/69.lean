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
# Ben Green's Open Problem 69

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.69)
- [ES13] Elekes, G. and Szabó, E., *On triple lines and cubic curves --- the Orchard problem
  revisited*. (2013). [arXiv:1302.5777](https://arxiv.org/abs/1302.5777)
- [GT13] Green, B. and Tao, T., *On sets defining few ordinary lines*. Discrete Comput. Geom. 50
  (2013), 409--468. [arXiv:1208.4714](https://arxiv.org/abs/1208.4714)
-/

@[expose] public section

open scoped Finset

namespace Green69

/--
`AtMostOnLine k A` says that no line contains more than $k$ points of `A`: every collinear subset
of `A` has at most $k$ points.
-/
def AtMostOnLine (k : ℕ) (A : Finset (ℝ × ℝ)) : Prop :=
  ∀ S ⊆ A, Collinear ℝ (S : Set (ℝ × ℝ)) → #S ≤ k

open scoped Classical in
/--
`numPairsWithThird A` is the number of ordered pairs $(x, y) \in A \times A$ of distinct points
such that the line $xy$ contains a third point of `A`.
-/
noncomputable def numPairsWithThird (A : Finset (ℝ × ℝ)) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 ≠ p.2 ∧ ∃ z ∈ A, z ≠ p.1 ∧ z ≠ p.2 ∧ z ∈ line[ℝ, p.1, p.2]}

/--
`OnCubic S` says that the points of `S` lie on a cubic curve: the zero set of a nonzero
polynomial $F(x, y)$ of total degree at most $3$ with real coefficients. A point $a$ is on the
curve if $F(a_1, a_2) = 0$.

This includes reducible cubics (a conic and a line, three lines) and curves of lower degree.
Requiring degree exactly $3$ gives the same notion, since multiplying $F$ by a linear polynomial
only enlarges its zero set.
-/
def OnCubic (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ 3 ∧
    ∀ a ∈ S, MvPolynomial.eval ![a.1, a.2] F = 0

/--
`tripleLines A` is the set of lines containing at least three points of `A`, called triple lines
in [ES13, Definition 1.2]. Each such line is the line through two distinct points of `A`, so the
set is finite and `Set.ncard` counts it.
-/
def tripleLines (A : Finset (ℝ × ℝ)) : Set (AffineSubspace ℝ (ℝ × ℝ)) :=
  {L | ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧ L = line[ℝ, x, y]}

/--
Fix a number $k$. Let $A \subset \mathbb{R}^2$ be a set of $n$ points, with no more than $k$ on
any line. Suppose that, for at least $\delta n^2$ pairs of points $(x, y) \in A \times A$, the
line $xy$ contains a third point of $A$. Is there some cubic curve containing at least $cn$
points of $A$, for some $c = c(k, \delta) > 0$?

We count ordered pairs of distinct points (`numPairsWithThird`), and a cubic curve is the zero set
of any nonzero real polynomial of degree at most $3$ (`OnCubic`), reducible ones included. The
constant $c$ depends only on $k$ and $\delta$. Small $n$ are harmless, since any $9$ points lie on
a cubic curve. [Gr24] notes that very little is known, except when $\delta = 1 - O(1/n)$, where the
statement follows from the main results of [GT13].
-/
@[category research open, question, AMS 5 14 52]
theorem green_69 :
    ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ A : Finset (ℝ × ℝ), AtMostOnLine k A →
      δ * (#A : ℝ) ^ 2 ≤ numPairsWithThird A → ∃ S ⊆ A, c * #A ≤ #S ∧ OnCubic S := by
  sorry

/--
**Elekes–Szabó conjecture.** If a set $H$ of points in the plane has at least $c|H|^2$ triple
lines (lines containing at least three points of $H$), then ten or more points of $H$ lie on a
(possibly degenerate) cubic, provided that $|H| > n_0(c)$ [ES13, Conjecture 2.1].

[Gr24] states it with $cn^2$ collinear triples in place of triple lines, and notes that it is much
weaker than `green_69` but should hold without the assumption of no more than $k$ points on a
line. The two forms are equivalent: $10$ collinear points lie on a cubic, and otherwise each
triple line contains at most $\binom{9}{3}$ collinear triples. The bound $n_0(c)$ is needed, since
a set of fewer than $10$ points can have $c|H|^2$ triple lines for small $c$. For points on an
irreducible curve of bounded degree, see [ES13, Theorem 2.2].
-/
@[category research open, AMS 5 14 52]
theorem green_69.variants.elekes_szabo :
    ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ A : Finset (ℝ × ℝ), n₀ < #A →
      c * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard → ∃ S ⊆ A, #S = 10 ∧ OnCubic S := by
  sorry

/-- A subset of a set of points on a cubic curve is on the same cubic curve. -/
@[category API, AMS 5 14]
theorem OnCubic.mono {S T : Finset (ℝ × ℝ)} (h : S ⊆ T) (hT : OnCubic T) : OnCubic S := by
  obtain ⟨F, hF, hdeg, hzero⟩ := hT
  exact ⟨F, hF, hdeg, fun a ha ↦ hzero a (h ha)⟩

end Green69
