/-
Copyright 2025 The Formal Conjectures Authors.

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
# Ben Green's Open Problem 57

*Reference:* [Ben Green's Open Problem 57](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 57)
-/

namespace Green57

open scoped Pointwise

noncomputable section

section

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Uniform average over pairs `(x₁, x₂)` in `G × G`, with the third variable determined by
the relation `x₁ + x₂ + x₃ = g`. -/
noncomputable def tripleKernel (f₁ f₂ f₃ : G × G → ℝ) : G → ℝ := fun g =>
  let cardG : ℝ := Fintype.card G
  (cardG ^ 2)⁻¹ *
      ∑ x₁ : G, ∑ x₂ : G,
        f₁ (x₂, g - x₁ - x₂) * f₂ (x₁, g - x₁ - x₂) * f₃ (x₁, x₂)

/-- Supremum norm bounded by `1`. -/
def LInftyBounded {α : Type*} (f : α → ℝ) : Prop := ∀ x, |f x| ≤ 1

/-- The generating family of functions for `Φ(G)`. -/
noncomputable def baseΦ :
    Set (G → ℝ) :=
  {φ | ∃ f₁ f₂ f₃ : G × G → ℝ,
      LInftyBounded f₁ ∧ LInftyBounded f₂ ∧ LInftyBounded f₃ ∧
      φ = tripleKernel G f₁ f₂ f₃}

/-- The generating family of functions for `Φ′(G)`, where the third kernel depends only on
`x₁ + x₂`. -/
noncomputable def baseΦ' :
    Set (G → ℝ) :=
  {φ | ∃ f₁ f₂ : G × G → ℝ, ∃ h : G → ℝ,
      LInftyBounded f₁ ∧ LInftyBounded f₂ ∧ LInftyBounded h ∧
      φ = tripleKernel G f₁ f₂ (fun p => h (p.1 + p.2))}

/-- The space `Φ(G)` of convex combinations of kernels from `baseΦ`. -/
noncomputable def Φ :
    Set (G → ℝ) :=
  convexHull ℝ (baseΦ G)

/-- The restricted space `Φ′(G)` of convex combinations of kernels from `baseΦ'`. -/
noncomputable def Φ' :
    Set (G → ℝ) :=
  convexHull ℝ (baseΦ' G)

/--
Is it true that for every finite abelian group $G$ the convex hulls $\Phi(G)$ and $\Phi'(G)$,
obtained from kernels $\phi(g) = \mathbb{E}_{x_1 + x_2 + x_3 = g} f_1(x_2, x_3)
      f_2(x_1, x_3) f_3(x_1, x_2)$ with $\lVert f_i \rVert_\infty \le 1$, still coincide when the
third kernel is required to depend only on $x_1 + x_2$?
-/
@[category research open, AMS 5 11]
theorem green_57 :
    answer(sorry) ↔
      ∀ (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G],
        Φ G = Φ' G := by
  sorry

end
