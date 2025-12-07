/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 602

*Reference:* [erdosproblems.com/602](https://www.erdosproblems.com/602)
-/

namespace Erdos602

open Cardinal

universe u v

variable (ι : Type u) (α : Type v) (A : ι → Set α) (h : ∀ i, #(A i) = ℵ₀)
variable (hij : ∀ i j, i ≠ j → ∃ n : ℕ, n ≠ 1 ∧ #{x : α // x ∈ (A i ∩ A j)} = n)

/--
**Erdős Problem 602:**
Let $(A_i)$ be a family of sets with $|A_i| = \aleph_0$ for all $i$, such that for any $i \neq j$ we have
$|A_i \cap A_j|$ finite and $\neq 1$.

Is there a $2$-colouring of $\bigcup_i A_i$ such that no $A_i$ is monochromatic?
-/
@[category research open, AMS 03 05]
theorem erdos_602 :
    ∃ (c : {x : α // ∃ i, x ∈ A i} → Fin 2),
    ∀ i, #(c '' fun ⟨x, _⟩ ↦ x ∈ A i) ≠ 1 := by
  sorry

end Erdos602
