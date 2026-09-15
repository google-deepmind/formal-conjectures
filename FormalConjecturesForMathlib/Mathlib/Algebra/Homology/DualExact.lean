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

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duals of exact complexes of vector spaces

Algebraic duality over a field takes an exact pair of linear maps to an exact pair in the
opposite direction. No finite-dimensionality hypothesis is needed: every functional on a
subspace of a vector space extends to the whole space.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace LinearMap

variable {R : Type u} [Field R]
  {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- Algebraic duality reverses an exact pair of linear maps. -/
lemma range_dualMap_eq_ker_dualMap_of_range_eq_ker
    (f : M₂ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₀)
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, ← h]

end LinearMap

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

/-- Applying algebraic duals to an exact short complex of vector spaces gives equality of the
new range and kernel. -/
lemma dual_range_eq_ker_of_exact
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    LinearMap.range S.g.hom.dualMap = LinearMap.ker S.f.hom.dualMap :=
  LinearMap.range_dualMap_eq_ker_dualMap_of_range_eq_ker
    S.f.hom S.g.hom hS.moduleCat_range_eq_ker

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]

/-- Exactness of a chain complex in degree `n + 1` becomes exactness of the algebraic-dual
cochain maps in the opposite direction. -/
lemma dual_differentials_range_eq_ker_of_exactAt
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hK : K.ExactAt (n + 1)) :
    LinearMap.range (K.d (n + 1) n).hom.dualMap =
      LinearMap.ker (K.d (n + 2) (n + 1)).hom.dualMap :=
  ShortComplex.dual_range_eq_ker_of_exact _
    ((K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).mp hK)

end HomologicalComplex
