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
# Smooth isometric embeddings of closed orientable surfaces in four-space

Does every closed orientable smooth surface, with any smooth Riemannian metric,
admit a smooth isometric embedding into $\mathbb{R}^4$? The Lean formalization [Ki26]
gives an affirmative answer. Gromov [Gr17] records the related immersion question
attributed to Chern.

*References:*
- [Gr17] M. Gromov, *Geometric, algebraic and analytic descendants of Nash isometric
  embedding theorems*, Bull. Amer. Math. Soc. (2017), footnote 6 and Question 55,
  https://www.ihes.fr/~gromov/category/hprinciple/.
- [Ki26] Kenta Kitamura, *smooth-isometric-embeddings-r4*, Lean formalization (2026),
  https://github.com/KitaKen1/smooth-isometric-embeddings-r4.
-/

@[expose] public section

namespace SmoothIsometricEmbeddingR4

open scoped ContDiff Manifold

/-- An orientation of the tangent spaces that is locally constant in every chart. -/
def IsOrientableSurface (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] : Prop :=
  ∃ o : M → Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2),
    ∀ p : M, IsLocallyConstant (fun x : (chartAt (EuclideanSpace ℝ (Fin 2)) p).source =>
      let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p) x.val
      Orientation.map (Fin 2)
        (D.toLinearMap.linearEquivOfInjective
          (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
            (by simpa only [extChartAt_source] using x.property)).injective rfl)
        (o x.val))

/-- Does every closed orientable smooth surface with any smooth Riemannian metric
admit a smooth isometric embedding into four-space? The answer is affirmative [Ki26]. -/
@[category research solved, AMS 53 58,
    formal_proof using lean4 at "https://github.com/KitaKen1/smooth-isometric-embeddings-r4/blob/b8ddbd009791591c817d5b18cb4eb6dd30039853/lean/FCSolution.lean#L11"]
theorem smooth_isometric_embedding_R4 :
    answer(True) ↔
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
        [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] [CompactSpace M] [T2Space M],
        IsOrientableSurface M →
          ∀ g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
              (EuclideanSpace ℝ (Fin 2))
              (fun p : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p),
            ∃ F : M → EuclideanSpace ℝ (Fin 4),
              ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
                  𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ F ∧ Function.Injective F ∧
                ∀ (p : M) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p),
                  let df := (NormedSpace.fromTangentSpace (F p)).toContinuousLinearMap.comp
                    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) F p)
                  inner ℝ (df v) (df w) = g.inner p v w := by
  sorry

end SmoothIsometricEmbeddingR4
