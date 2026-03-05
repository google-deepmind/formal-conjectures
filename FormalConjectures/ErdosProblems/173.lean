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
# Erdős Problem 173

*Reference:* [erdosproblems.com/173](https://www.erdosproblems.com/173)

In any 2-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$ (up to congruence),
there is a monochromatic congruent copy of $T$.

For some colourings a single equilateral triangle has to be excluded (considering
the colouring by alternating strips). Shader [Sh76] proved this is true for any
single right-angled triangle.

[Er75f] Erdős, P.

[ErGr79] Erdős, P. and Graham, R.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[Er83c] Erdős, P.

[Sh76] Shader, L.
-/

namespace Erdos173

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def euclideanDistSq (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The multiset of squared side lengths of a triangle. Two triangles are congruent
    (by SSS) iff their squared side length multisets are equal. -/
noncomputable def triangleSideSqs (p₁ p₂ p₃ : ℝ × ℝ) : Multiset ℝ :=
  ↑[euclideanDistSq p₁ p₂, euclideanDistSq p₂ p₃, euclideanDistSq p₁ p₃]

/-- A triangle is non-degenerate if its vertices are not collinear. -/
def TriangleNonDegenerate (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  (p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2) ≠ 0

/--
Erdős Conjecture (Problem 173) [Er75f, ErGr79, ErGr80, Er83c]:

In any 2-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$ (up to congruence),
there is a monochromatic congruent copy of $T$.

Equivalently: if two non-degenerate triangles both fail to have any monochromatic
congruent copy under some 2-colouring, then they must be congruent.
-/
@[category research open, AMS 5 51]
theorem erdos_173 :
    ∀ f : ℝ × ℝ → Bool,
    ∀ p₁ p₂ p₃ q₁ q₂ q₃ : ℝ × ℝ,
    TriangleNonDegenerate p₁ p₂ p₃ →
    TriangleNonDegenerate q₁ q₂ q₃ →
    (∀ a₁ a₂ a₃ : ℝ × ℝ, triangleSideSqs a₁ a₂ a₃ = triangleSideSqs p₁ p₂ p₃ →
      ¬(f a₁ = f a₂ ∧ f a₂ = f a₃)) →
    (∀ b₁ b₂ b₃ : ℝ × ℝ, triangleSideSqs b₁ b₂ b₃ = triangleSideSqs q₁ q₂ q₃ →
      ¬(f b₁ = f b₂ ∧ f b₂ = f b₃)) →
    triangleSideSqs p₁ p₂ p₃ = triangleSideSqs q₁ q₂ q₃ := by
  sorry

end Erdos173
