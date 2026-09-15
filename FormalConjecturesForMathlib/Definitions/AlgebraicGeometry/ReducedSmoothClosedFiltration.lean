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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ReducedSmoothStratification
/-!
# The canonical smooth decomposition as a closed filtration

This module indexes the already constructed recursive smooth decomposition by natural
numbers. Consecutive closed supports differ by the actual smooth piece. The filtration
is empty at the length of the existing finite list and stays empty thereafter. This
format exposes precisely the nested closed supports required for localization induction;
it introduces no stratification choices or assumed cohomology vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- Iteration of the actual reduced singular remainder, padded only by empty supports
after the already constructed finite decomposition terminates. -/
def reducedSmoothClosedFiltration (S : Closeds X) : ℕ → Closeds X
  | 0 => S
  | k + 1 => reducedClosedSingularRemainder f (reducedSmoothClosedFiltration S k)

variable [PerfectField K] [NoetherianSpace X]

end AlgebraicGeometry
