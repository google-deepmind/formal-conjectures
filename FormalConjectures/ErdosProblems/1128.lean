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

/-!
# Erdős Problem 1128

Erdős and Hajnal asked whether any 2-colouring of the product of three sets of cardinality ℵ₁
must contain a monochromatic countably infinite sub-product. This was disproved by Prikry and
Mills (1978).

*Reference:* [erdosproblems.com/1128](https://www.erdosproblems.com/1128)

[Er81b] Erdős, P., *Problems and results on finite and infinite combinatorial analysis*, p.33.
-/

open Cardinal

namespace Erdos1128

/--
A problem of Erdős and Hajnal [Er81b,p.33]. Let $A$, $B$, $C$ be three sets of cardinality
$\aleph_1$. Is it true that, in any $2$-colouring of $A \times B \times C$, there must exist
$A_1 \subset A$, $B_1 \subset B$, $C_1 \subset C$, all of cardinality $\aleph_0$, such that
$A_1 \times B_1 \times C_1$ is monochromatic?

The answer is no. This was disproved by Prikry and Mills in 1978
(unpublished), as reported by Todorčević and Komjáth.
-/
@[category research solved, AMS 3 5]
theorem erdos_1128 : answer(False) ↔
    ∀ (α β γ : Type) (_ : #α = aleph 1) (_ : #β = aleph 1) (_ : #γ = aleph 1)
      (f : α × β × γ → Fin 2),
      ∃ (A₁ : Set α) (B₁ : Set β) (C₁ : Set γ),
        #A₁ = aleph 0 ∧ #B₁ = aleph 0 ∧ #C₁ = aleph 0 ∧
        ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ z ∈ C₁, f (a, b, z) = c := by
  sorry

end Erdos1128
