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

public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Promise problems and polynomial-time reductions

A promise problem has disjoint sets of yes and no instances. Reductions must send every promised
source instance to the corresponding promise of the target. Hardness means that every language in
`ComplexityTheory.NP` admits such a polynomial-time reduction.

Reference: S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, 2009, Chapter 2.
-/

@[expose] public section

namespace ComplexityTheory

/-- Disjoint yes and no instances; inputs outside their union have no prescribed answer. -/
structure PromiseProblem (α : Type*) where
  yes : Set α
  no : Set α
  disjoint : Disjoint yes no

namespace PromiseProblem

/-- A polynomial-time many-one reduction preserving both promises. -/
def PolyTimeReduces {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (P : PromiseProblem α) (Q : PromiseProblem β) : Prop :=
  ∃ f : α → β, IsPolyTime f ∧ (∀ x ∈ P.yes, f x ∈ Q.yes) ∧
    ∀ x ∈ P.no, f x ∈ Q.no

/-- A decision problem considered as a promise problem with every input promised. -/
def ofDecisionProblem (L : DecisionProblem) : PromiseProblem (List Bool) where
  yes := {x | L x = true}
  no := {x | L x = false}
  disjoint := Set.disjoint_left.mpr fun _ h₁ h₂ ↦ by simp_all

/-- NP-hardness under polynomial-time promise-preserving many-one reductions. -/
def IsNPHard {α : Type} [BitstringEncoding α] (P : PromiseProblem α) : Prop :=
  ∀ L ∈ NP, (ofDecisionProblem L).PolyTimeReduces P

/-- Every promise problem reduces to itself. -/
theorem polyTimeReduces_refl {α : Type} [BitstringEncoding α] (P : PromiseProblem α) :
    P.PolyTimeReduces P :=
  ⟨id, isPolyTime_id, fun _ h ↦ h, fun _ h ↦ h⟩

end PromiseProblem
end ComplexityTheory
