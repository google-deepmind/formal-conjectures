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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiGlobalSectionsComparison

/-!
# Betti cohomology and global sections

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiGlobalSectionsComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c)
  (e : c.Embedding c') [e.IsRelIff]

end HomologicalComplex

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

end CochainComplex.HomComplex

namespace TopCat.Sheaf

section

variable {Y : TopCat.{0}}

end

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (Y : TopCat.{u})

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- Every positive sheaf-cohomology class of every term of the rational singular-cochain
resolution vanishes on a hereditarily paracompact Hausdorff space. -/
theorem rationalSingularCochainTerm_cohomology_succ_eq_zero
    (Y : TopCat.{0}) [T2Space Y] [∀ U : Opens Y, ParacompactSpace U]
    (p q : ℕ) (x : Abelian.Ext
      (TopCat.Sheaf.IsFlasque.globalSectionsSource (X := Y))
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ Y p) (q + 1)) :
    x = 0 :=
  AlgebraicTopology.Singular.singularCochainSheaf_cohomology_succ_eq_zero p q x

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

end AlgebraicGeometry.ComplexPoint
