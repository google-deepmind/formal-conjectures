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

import FormalConjecturesUtil

/-!
# Erdős Problem 603

*References:*
- [erdosproblems.com/603](https://www.erdosproblems.com/603)
-/

namespace Erdos603

open Cardinal Filter Asymptotics

/--
Let $(A_i)$ be a family of countably infinite sets such that $\lvert A_i\cap A_j\rvert \neq 2$ for
all $i\neq j$. Find the smallest cardinal $C$ such that $\cup A_i$ can always be coloured with at
most $C$ colours so that no $A_i$ is monochromatic.

GPT 5.4 Pro (prompted by Chojecki) proved there is no uniform bound on such $C$: for every cardinal
$C$ there is a family of countably infinite sets $(A_i)$ such that $\lvert A_i\cap A_j\rvert \neq 2$
for all $i\neq j$, and in any colouring of $\cup A_i$ with $C$ colours some $A_i$ is monochromatic.
-/
@[category research solved, AMS 3 5]
theorem erdos_603 :
    ∀ C : Cardinal.{0}, ∃ (V : Type) (F : Set (Set V)),
    (∀ A ∈ F, Cardinal.mk A = ℵ₀) ∧
    F.Pairwise (fun (A B : Set V) ↦ Cardinal.mk ↥(A ∩ B) ≠ 2) ∧
    ⋃₀ F = Set.univ ∧
    ∀ c : V → C.out, ∃ A ∈ F, ∀ x ∈ A, ∀ y ∈ A, c x = c y := by
  sorry

end Erdos603
