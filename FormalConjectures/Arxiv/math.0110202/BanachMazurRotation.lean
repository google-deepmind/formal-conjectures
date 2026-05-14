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

open TopologicalSpace Metric MulAction

/-!
# Banach-Mazur Rotation Problem

*References:*
- [arxiv/math.0110202](https://arxiv.org/abs/math/0110202)
  **A note on Banach--Mazur problem** by *Beata Randrianantoanina*
- [mathoverflow/41211](https://mathoverflow.net/questions/41211/easy-proof-of-the-fact-that-isotropic-spaces-are-euclidean)
  **Easy proof of the fact that isotropic spaces are Euclidean**
-/

namespace Arxiv.«math.0110202»

/-- The group of linear isometric equivalences acts on the unit sphere by evaluation. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    MulAction (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1) where
  smul T x := ⟨T x, mem_sphere_zero_iff_norm.2 <| by simp⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
The Banach--Mazur rotation problem asks whether every separable Banach space whose group of linear
isometric equivalences acts transitively on the unit sphere is linearly isometric to a Hilbert
space.
-/
@[category research open, AMS 46]
theorem banach_mazur_rotation_problem : answer(sorry) ↔
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
      [IsPretransitive (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1)], ∃ (H : Type*) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℝ H),
      Nonempty (E ≃ₗᵢ[ℝ] H) := by
  sorry

/-- Every finite-dimensional real normed space whose isometry group acts transitively on the
unit sphere is Euclidean. -/
@[category research solved, AMS 46]
theorem banach_mazur_rotation_problem.finite_dimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsPretransitive (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1)] :
    InnerProductSpaceable E := by
  sorry

end Arxiv.«math.0110202»
