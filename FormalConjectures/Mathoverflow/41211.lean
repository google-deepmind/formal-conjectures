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
# Mathoverflow 41211

*References:*
- [](https://arxiv.org/pdf/math/0110202)
- [mathoverflow/41211](https://mathoverflow.net/questions/41211/easy-proof-of-the-fact-that-isotropic-spaces-are-euclidean)

-/

namespace Mathoverflow41211

/-- The group of linear isometry equivalences acts on the unit sphere by evaluation. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    MulAction (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1) where
  smul T x := ⟨T x, mem_sphere_zero_iff_norm.2 <| by simp⟩
  one_smul _ := Subtype.ext <| rfl
  mul_smul _ _ _ := Subtype.ext <| rfl

/-- Assume `E` is a separable Banach space whose group of linear isometry equivalences acts
transitively on the unit sphere. Is `E` linearly isomorphic to a separable Hilbert space? -/
@[category research open, AMS 46]
theorem mathoverflow_41211 : answer(sorry) ↔
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
      [IsPretransitive (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1)], ∃ (H : Type*) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H) (_ : SeparableSpace H),
      Nonempty (E ≃ₗᵢ[ℝ] H) := by
  sorry

/-- Every finite-dimensional real normed space whose isometry group acts transitively on the
unit sphere is Euclidean. -/
@[category research solved, AMS 46 52]
theorem mathoverflow_41211.finite_dimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsPretransitive (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1)] :
    InnerProductSpace ℝ E := by
  sorry

end Mathoverflow41211
