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
# Erdős Problem 634

*Reference:* [erdosproblems.com/634](https://www.erdosproblems.com/634)

Find all $n$ such that there is at least one triangle which can be cut into $n$
congruent triangles.

[So09c] Soifer, A., *Is There Anything Beyond the Solution?*, The Mathematical Coloring
Book, Springer, 2009, pp. 47–50.
[SWW91] Snover, S., Waiveris, C., Williams, J., *Rep-tiling for triangles*,
Discrete Mathematics (1991), 193–200.
[Zh25] Zhang, Y., *Tiling Triangles With 2π/3 Angles*, arXiv:2512.22696, 2025.
-/

open scoped EuclideanGeometry

namespace Erdos634

/-- Multiset of side lengths of a triangle with vertices `T : Fin 3 → ℝ²`.
    Two triangles are congruent (by SSS) iff these multisets agree. -/
noncomputable def sideLengths (T : Fin 3 → ℝ²) : Multiset ℝ :=
  ↑[dist (T 0) (T 1), dist (T 1) (T 2), dist (T 0) (T 2)]

/-- Triangle `T` can be dissected into exactly `n` pairwise-congruent
    non-degenerate triangles that tile it: each piece has affinely independent
    vertices, all pieces are congruent, each is contained in the original,
    their interiors are pairwise disjoint, and their union covers the original. -/
def CanDissectInto (T : Fin 3 → ℝ²) (n : ℕ) : Prop :=
  ∃ (V : Fin n → Fin 3 → ℝ²),
    (∀ i, AffineIndependent ℝ (V i)) ∧
    (∀ i j, sideLengths (V i) = sideLengths (V j)) ∧
    (∀ i, convexHull ℝ (Set.range (V i)) ⊆ convexHull ℝ (Set.range T)) ∧
    (∀ i j, i ≠ j →
      interior (convexHull ℝ (Set.range (V i))) ∩
      interior (convexHull ℝ (Set.range (V j))) = ∅) ∧
    (∀ p, p ∈ convexHull ℝ (Set.range T) →
      ∃ i, p ∈ convexHull ℝ (Set.range (V i)))

/-- There exists a triangle that can be dissected into `n` congruent triangles. -/
def HasCongruentDissection (n : ℕ) : Prop :=
  ∃ T : Fin 3 → ℝ², AffineIndependent ℝ T ∧ CanDissectInto T n

/-- Two triangles are similar if their side length multisets are proportional. -/
noncomputable def AreSimilar (T₁ T₂ : Fin 3 → ℝ²) : Prop :=
  ∃ c : ℝ, 0 < c ∧ sideLengths T₁ = (sideLengths T₂).map (c * ·)

/-- Triangle `T` can be dissected into `n` pairwise-similar non-degenerate triangles. -/
def CanDissectIntoSimilar (T : Fin 3 → ℝ²) (n : ℕ) : Prop :=
  ∃ (V : Fin n → Fin 3 → ℝ²),
    (∀ i, AffineIndependent ℝ (V i)) ∧
    (∀ i j, AreSimilar (V i) (V j)) ∧
    (∀ i, convexHull ℝ (Set.range (V i)) ⊆ convexHull ℝ (Set.range T)) ∧
    (∀ i j, i ≠ j →
      interior (convexHull ℝ (Set.range (V i))) ∩
      interior (convexHull ℝ (Set.range (V j))) = ∅) ∧
    (∀ p, p ∈ convexHull ℝ (Set.range T) →
      ∃ i, p ∈ convexHull ℝ (Set.range (V i)))

/-- Triangle `T` can be dissected into `n` non-degenerate triangles each similar to `T`. -/
def CanDissectIntoSelfSimilar (T : Fin 3 → ℝ²) (n : ℕ) : Prop :=
  ∃ (V : Fin n → Fin 3 → ℝ²),
    (∀ i, AffineIndependent ℝ (V i)) ∧
    (∀ i, AreSimilar (V i) T) ∧
    (∀ i, convexHull ℝ (Set.range (V i)) ⊆ convexHull ℝ (Set.range T)) ∧
    (∀ i j, i ≠ j →
      interior (convexHull ℝ (Set.range (V i))) ∩
      interior (convexHull ℝ (Set.range (V j))) = ∅) ∧
    (∀ p, p ∈ convexHull ℝ (Set.range T) →
      ∃ i, p ∈ convexHull ℝ (Set.range (V i)))

/-- There exists a triangle that can be dissected into `n` triangles similar to itself. -/
def HasSelfSimilarDissection (n : ℕ) : Prop :=
  ∃ T : Fin 3 → ℝ², AffineIndependent ℝ T ∧ CanDissectIntoSelfSimilar T n

/--
Erdős Problem 634: It is conjectured that no prime $p \equiv 3 \pmod{4}$
has the property that some triangle can be cut into $p$ congruent triangles.
-/
@[category research open, AMS 52]
theorem erdos_634 :
    ∀ p : ℕ, Nat.Prime p → p % 4 = 3 → ¬ HasCongruentDissection p := by
  sorry

/--
Every perfect square $n^2$ (with $n \ge 1$) has a congruent dissection:
any triangle can be cut into $n^2$ congruent copies. (Folklore)
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (n ^ 2) := by
  sorry

/--
For any positive integer $n$, the number $2n^2$ has a congruent dissection. [So09c]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.two_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (2 * n ^ 2) := by
  sorry

/--
For any positive integer $n$, the number $3n^2$ has a congruent dissection. [So09c]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.three_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (3 * n ^ 2) := by
  sorry

/--
For any positive integer $n$, the number $6n^2$ has a congruent dissection. [So09c]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.six_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (6 * n ^ 2) := by
  sorry

/--
For any positive integers $n$ and $m$, the number $n^2 + m^2$ has a congruent
dissection. [So09c]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.sum_of_squares (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    HasCongruentDissection (n ^ 2 + m ^ 2) := by
  sorry

/--
There is no triangle that can be cut into exactly $7$ congruent triangles. (Beeson)
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.not_seven : ¬ HasCongruentDissection 7 := by
  sorry

/--
There is no triangle that can be cut into exactly $11$ congruent triangles. (Beeson)
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.not_eleven : ¬ HasCongruentDissection 11 := by
  sorry

/--
Zhang [Zh25] proved that for integers $a \ge b \ge 1$, if
$n \ge 3\lceil(a^2 + b^2 + ab - a - b)/(ab)\rceil$, then $n^2 ab$ has a
congruent dissection.
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.zhang (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : b ≤ a)
    (hn : 3 * ⌈((a : ℚ) ^ 2 + b ^ 2 + a * b - a - b) / (a * b)⌉₊ ≤ n) :
    HasCongruentDissection (n ^ 2 * a * b) := by
  sorry

/--
Every triangle can be cut into $N$ similar (not necessarily congruent) triangles
for all $N \ne 2, 3, 5$. [So09c]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.similar (T : Fin 3 → ℝ²) (hT : AffineIndependent ℝ T)
    (n : ℕ) (hn₁ : 1 ≤ n) (hn₂ : n ≠ 2) (hn₃ : n ≠ 3) (hn₅ : n ≠ 5) :
    CanDissectIntoSimilar T n := by
  sorry

/--
If the smaller triangles must be similar to the original triangle, the possible
values of $n$ are exactly those of the form $k^2$, $k^2 + m^2$, or $3k^2$
for positive integers $k, m$. [SWW91]
-/
@[category research solved, AMS 52]
theorem erdos_634.variants.self_similar_characterization (n : ℕ) :
    HasSelfSimilarDissection n ↔
    (∃ k : ℕ, 1 ≤ k ∧ n = k ^ 2) ∨
    (∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ n = k ^ 2 + m ^ 2) ∨
    (∃ k : ℕ, 1 ≤ k ∧ n = 3 * k ^ 2) := by
  sorry

/--
The case $n = 19$ is the smallest open case: it is unknown whether any triangle
can be cut into exactly $19$ congruent triangles. Since $19 \equiv 3 \pmod{4}$
is prime, the main conjecture predicts this is impossible.
-/
@[category research open, AMS 52]
theorem erdos_634.variants.not_nineteen : ¬ HasCongruentDissection 19 := by
  sorry

end Erdos634
