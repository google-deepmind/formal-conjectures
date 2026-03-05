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

[So09c] Soifer, A., *The Mathematical Coloring Book*, Springer, 2009.
-/

namespace Erdos634

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Multiset of squared side lengths of a triangle.
    Two triangles are congruent (by SSS) iff these multisets agree. -/
noncomputable def sideLengthsSq (A B C : ℝ × ℝ) : Multiset ℝ :=
  ↑[sqDist A B, sqDist B C, sqDist A C]

/-- A triangle is non-degenerate (vertices not collinear). -/
def NonDegenerate (A B C : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- The closed triangular region: convex hull of vertices $A$, $B$, $C$.
    A point $p$ lies in the triangle iff $p = \alpha A + \beta B + \gamma C$ for some
    $\alpha, \beta, \gamma \ge 0$ with $\alpha + \beta + \gamma = 1$. -/
def triangleRegion (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- The open interior of a triangular region: strictly positive
    barycentric coordinates. -/
def triangleInterior (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- Triangle $(A, B, C)$ can be dissected into exactly $n$ pairwise-congruent
    non-degenerate triangles that tile it: each is contained in the original,
    their interiors are pairwise disjoint, and their union covers the original. -/
def CanDissectInto (A B C : ℝ × ℝ) (n : ℕ) : Prop :=
  ∃ (V : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)),
    (∀ i, NonDegenerate (V i).1 (V i).2.1 (V i).2.2) ∧
    (∀ i j, sideLengthsSq (V i).1 (V i).2.1 (V i).2.2 =
            sideLengthsSq (V j).1 (V j).2.1 (V j).2.2) ∧
    (∀ i, triangleRegion (V i).1 (V i).2.1 (V i).2.2 ⊆
           triangleRegion A B C) ∧
    (∀ i j, i ≠ j →
      triangleInterior (V i).1 (V i).2.1 (V i).2.2 ∩
      triangleInterior (V j).1 (V j).2.1 (V j).2.2 = ∅) ∧
    (∀ p, p ∈ triangleRegion A B C →
      ∃ i, p ∈ triangleRegion (V i).1 (V i).2.1 (V i).2.2)

/-- There exists a triangle that can be dissected into $n$ congruent triangles. -/
def HasCongruentDissection (n : ℕ) : Prop :=
  ∃ A B C : ℝ × ℝ, NonDegenerate A B C ∧ CanDissectInto A B C n

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

end Erdos634
