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
# Ben Green's Open Problem 75

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.75)
- [CL25] Conlon, D. and Lim, J., *Everywhere unbalanced configurations*. Adv. Math. 480 (2025),
  Paper No. 110445. [arXiv:2308.02466](https://arxiv.org/abs/2308.02466)
- [Pi03] Pinchasi, R., *Lines with many points on both sides*. Discrete Comput. Geom. 30 (2003),
  415-435. [doi:10.1007/s00454-003-2826-8](https://doi.org/10.1007/s00454-003-2826-8)
-/

@[expose] public section

open scoped Finset

namespace Green75

/--
`cross p q x` is the cross product $(q - p) \times (x - p)$. For $p \neq q$ it is positive if `x`
lies strictly to the left of the line from `p` to `q`, negative if `x` lies strictly to the right,
and zero if `x` lies on the line `pq`.
-/
def cross (p q x : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (x.2 - p.2) - (q.2 - p.2) * (x.1 - p.1)

/-- The number of points of `X` strictly to the left of the line from `p` to `q`. -/
noncomputable def leftCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | 0 < cross p q x}

/-- The number of points of `X` strictly to the right of the line from `p` to `q`. -/
noncomputable def rightCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | cross p q x < 0}

/--
`imbalance X p q` is the absolute difference between the numbers of points of `X` on the two sides
of the line through
`p` and `q`. The points of `X` on the line itself are on neither side.
-/
noncomputable def imbalance (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℤ :=
  |(leftCount X p q : ℤ) - (rightCount X p q : ℤ)|

/--
Let $X \subset \mathbb{R}^2$ be a set of $n$ points. Does there exist a line $\ell$ through at
least two points of $X$ such that the numbers of points on either side of $\ell$ differ by at
most $100$?

This is a form of the Kupitz-Perles conjecture [Gr24]. We take $n \geq 2$, since a line through
two points of $X$ needs two points. If all points of $X$ are collinear, the line through them has
no points on either side.
-/
@[category research open, question, AMS 5 52]
theorem green_75 :
    ∀ X : Finset (ℝ × ℝ), 2 ≤ #X → ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ 100 := by
  sorry

/--
Is there a constant $C$ such that every finite set $X \subset \mathbb{R}^2$ with at least two
points has a line through two points of $X$ whose sides differ by at most $C$? This is the
question of Kupitz in the form of [CL25, Section 1], where the constant is not specified.

`green_75` implies it with $C = 100$.
-/
@[category research open, question, AMS 5 52]
theorem green_75.variants.exists_constant :
    ∃ C : ℕ, ∀ X : Finset (ℝ × ℝ), 2 ≤ #X →
      ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ C := by
  sorry

/--
Pinchasi [Pi03] proved that the answer to `green_75` is yes if $100$ is replaced by
$C \log \log n$ for an absolute constant $C$, where $n = |X|$ [Gr24]. This is the best known bound.
[CL25, Theorem 1.1] states Pinchasi's theorem for generalised configurations (points with
pseudolines); sets of points with lines are a special case. The hypothesis $n \geq 3$ ensures
that $\log \log n > 0$.
-/
@[category research solved, AMS 5 52]
theorem green_75.variants.pinchasi :
    ∃ C : ℝ, ∀ X : Finset (ℝ × ℝ), 3 ≤ #X → ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧
      (imbalance X p q : ℝ) ≤ C * Real.log (Real.log #X) := by
  sorry

/--
Kupitz conjectured that one can take the difference to be at most $1$ [CL25, Section 1]. Alon
showed that this is false: there are finite point sets for which, for every line through two of
its points, the numbers of points on the two sides differ by at least $2$ [CL25, Section 1].
[Gr24] phrases this as: the answer to `green_75` is no if $100$ is replaced by $2$. Since the
sets in [CL25] have differences of at least $2$, they show that $100$ cannot be replaced by $1$.
We state the form given in [CL25].
-/
@[category research solved, AMS 5 52]
theorem green_75.variants.alon :
    ∃ X : Finset (ℝ × ℝ), 2 ≤ #X ∧ ∀ p ∈ X, ∀ q ∈ X, p ≠ q → 2 ≤ imbalance X p q := by
  sorry

/-- The point `p` is on neither side of a line through `p`. -/
@[category API, AMS 5 52]
theorem cross_self_left (p q : ℝ × ℝ) : cross p q p = 0 := by
  unfold cross
  ring

/-- The point `q` is on neither side of a line through `q`. -/
@[category API, AMS 5 52]
theorem cross_self_right (p q : ℝ × ℝ) : cross p q q = 0 := by
  unfold cross
  ring

/--
For a set of two points, the line through them has no points on either side. So `green_75` has
content only for $n \geq 3$.
-/
@[category test, AMS 5 52]
theorem imbalance_pair (p q : ℝ × ℝ) : imbalance {p, q} p q = 0 := by
  have hl : leftCount {p, q} p q = 0 := by
    unfold leftCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h, cross_self_left]
      exact lt_irrefl _
    · rw [Finset.mem_singleton.1 h, cross_self_right]
      exact lt_irrefl _
  have hr : rightCount {p, q} p q = 0 := by
    unfold rightCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h, cross_self_left]
      exact lt_irrefl _
    · rw [Finset.mem_singleton.1 h, cross_self_right]
      exact lt_irrefl _
  simp [imbalance, hl, hr]

end Green75
