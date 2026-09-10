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

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Quasi-isomorphisms on kernels in a morphism of short exact complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- In a morphism of short exact sequences of cochain complexes, if the middle
and last maps are quasi-isomorphisms, so is the first map. -/
lemma quasiIso_first_of_shortExact
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) [QuasiIso f.τ₂] [QuasiIso f.τ₃] :
    QuasiIso f.τ₁ := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).mp
  exact isIso₁_of_isIso₂₃ (DerivedCategory.triangleOfSES.map hS hT f)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hT)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₂)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₃)))

end CochainComplex
