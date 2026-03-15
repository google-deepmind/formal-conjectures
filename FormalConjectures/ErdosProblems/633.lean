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
# Erdős Problem 633

*Reference:* [erdosproblems.com/633](https://www.erdosproblems.com/633)

Classify those triangles which can only be cut into a square number of congruent
triangles. **$25 reward.**

Any triangle can be cut into $n^2$ congruent triangles for any $n \geq 1$ [So09].
Soifer [So09c] reported Erdős's question and proved that there exists at least one
triangle (e.g. one with sides $\sqrt{2}$, $\sqrt{3}$, $\sqrt{4}$) which can only be cut
into a square number of congruent triangles. In fact, Soifer [So09b] proved that any
triangle for which the angles and sides are both integrally independent has this property.
The full classification remains open.

See also Problem 634 for related results on which numbers $n$ admit a congruent dissection
of an equilateral triangle.

[So09] Soifer, A., *How Does One Cut a Triangle? I*, The Mathematical Coloring Book,
Springer, 2009, pp. 15–23.
[So09b] Soifer, A., *How Does One Cut a Triangle? II*, The Mathematical Coloring Book,
Springer, 2009, pp. 37–39.
[So09c] Soifer, A., *Is There Anything Beyond the Solution?*, The Mathematical Coloring
Book, Springer, 2009, pp. 47–50.
-/

namespace Erdos633

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
$\alpha, \beta, \gamma \geq 0$ with $\alpha + \beta + \gamma = 1$. -/
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
    -- All sub-triangles are non-degenerate
    (∀ i, NonDegenerate (V i).1 (V i).2.1 (V i).2.2) ∧
    -- All sub-triangles are mutually congruent (same squared side lengths)
    (∀ i j, sideLengthsSq (V i).1 (V i).2.1 (V i).2.2 =
            sideLengthsSq (V j).1 (V j).2.1 (V j).2.2) ∧
    -- Each sub-triangle is contained in the original
    (∀ i, triangleRegion (V i).1 (V i).2.1 (V i).2.2 ⊆
           triangleRegion A B C) ∧
    -- Pairwise disjoint interiors
    (∀ i j, i ≠ j →
      triangleInterior (V i).1 (V i).2.1 (V i).2.2 ∩
      triangleInterior (V j).1 (V j).2.1 (V j).2.2 = ∅) ∧
    -- Union covers the original triangle
    (∀ p, p ∈ triangleRegion A B C →
      ∃ i, p ∈ triangleRegion (V i).1 (V i).2.1 (V i).2.2)

/-- Euclidean distance (side length) between two points. -/
noncomputable def sideLength (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist p q)

/-- The sides of a triangle are integrally independent: no nontrivial integer
linear combination of the three side lengths equals zero. -/
def IntIndepSides (A B C : ℝ × ℝ) : Prop :=
  ∀ (a₁ a₂ a₃ : ℤ),
    ↑a₁ * sideLength B C + ↑a₂ * sideLength A C +
      ↑a₃ * sideLength A B = 0 →
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0

/-- The angle at vertex $P$ in triangle $PQR$, via the dot-product formula:
$\arccos\bigl(\frac{\vec{PQ} \cdot \vec{PR}}{|PQ| \cdot |PR|}\bigr)$.
Returns a value in $[0, \pi]$. -/
noncomputable def angle (P Q R : ℝ × ℝ) : ℝ :=
  Real.arccos (((Q.1 - P.1) * (R.1 - P.1) + (Q.2 - P.2) * (R.2 - P.2)) /
    (sideLength P Q * sideLength P R))

/-- The angles of a triangle are integrally independent: the only integer
linear combination of the angles that equals an integer multiple of $\pi$
is the trivial one (all coefficients equal). This accounts for the
constraint $\alpha + \beta + \gamma = \pi$. -/
def IntIndepAngles (A B C : ℝ × ℝ) : Prop :=
  ∀ (a₁ a₂ a₃ k : ℤ),
    ↑a₁ * angle A B C + ↑a₂ * angle B A C +
      ↑a₃ * angle C A B = ↑k * Real.pi →
    a₁ = a₂ ∧ a₂ = a₃

/--
Every non-degenerate triangle can be dissected into $n^2$ congruent triangles
for any positive integer $n$.
-/
@[category research solved, AMS 51]
theorem erdos_633.variants.square_dissection
    (A B C : ℝ × ℝ) (hnd : NonDegenerate A B C)
    (n : ℕ) (hn : 1 ≤ n) :
    CanDissectInto A B C (n ^ 2) := by
  sorry

/--
There exists a non-degenerate triangle which can be dissected into $n$
congruent triangles only when $n$ is a perfect square. [So09c]
-/
@[category research solved, AMS 51]
theorem erdos_633.variants.existence :
    ∃ A B C : ℝ × ℝ, NonDegenerate A B C ∧
    ∀ n : ℕ, 1 ≤ n → CanDissectInto A B C n → ∃ m : ℕ, n = m ^ 2 := by
  sorry

/--
If a non-degenerate triangle has integrally independent sides and angles,
then it can only be dissected into a perfect square number of congruent
triangles. [So09b]
-/
@[category research solved, AMS 51]
theorem erdos_633.variants.soifer
    (A B C : ℝ × ℝ) (hnd : NonDegenerate A B C)
    (hsides : IntIndepSides A B C) (hangles : IntIndepAngles A B C) :
    ∀ n : ℕ, 1 ≤ n → CanDissectInto A B C n → ∃ m : ℕ, n = m ^ 2 := by
  sorry

/--
Classify those non-degenerate triangles that can only be cut into a perfect
square number of congruent triangles. The full classification remains open.
-/
@[category research open, AMS 51]
theorem erdos_633 :
    {T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) |
      NonDegenerate T.1 T.2.1 T.2.2 ∧
      ∀ n, 1 ≤ n → CanDissectInto T.1 T.2.1 T.2.2 n → ∃ m, n = m ^ 2} =
    answer(sorry) := by sorry

end Erdos633
