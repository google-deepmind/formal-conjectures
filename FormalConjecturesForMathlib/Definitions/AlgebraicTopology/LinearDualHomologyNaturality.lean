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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainCohomology
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.LinearDualNaturality

/-! # Naturality of the actual universal-coefficient pairing -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The actual cochain-complex universal-coefficient identification. -/
def linearDualHomologyEquiv (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.homology n ≃ₗ[R] Module.Dual R (K.homology n) :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.trans
    (K.sc n).linearDualHomologyEquiv

end HomologicalComplex
