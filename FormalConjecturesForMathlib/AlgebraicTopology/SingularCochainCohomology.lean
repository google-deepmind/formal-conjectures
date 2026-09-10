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

public import FormalConjecturesForMathlib.Algebra.Homology.LinearDual
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology

/-!
# Cohomology of singular cochains

This file defines ordinary singular cochain cohomology as the homology of the algebraic dual of
the singular chain complex. The universal-coefficient identification of
`FormalConjecturesForMathlib.Algebra.Homology.LinearDual` then identifies it with the singular
cohomology of `FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology`, which is defined
directly as the dual of homology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Ordinary singular cochain cohomology in degree `n`, expressed as the homology of the
algebraic-dual short complex centered on the singular chain group in degree `n`. -/
abbrev CochainCohomology (n : ℕ) : ModuleCat.{u} R :=
  let K :=
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X
  (K.sc n).linearDual.homology

/-- The universal-coefficient equivalence from ordinary singular cochain cohomology to the
linear dual of singular homology. -/
def cochainCohomologyEquiv (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R] Cohomology R X n :=
  let K :=
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X
  (K.sc n).linearDualHomologyEquiv

end AlgebraicTopology.Singular
