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

/--
A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

set_option linter.unusedVariables false

/--
A028859 Conjecture: Also the number of length $n + 1$ sequences that cover an initial
interval of positive integers and whose non-adjacent parts are weakly decreasing.

Formally: The cardinality of the set of sequences $\sigma : \text{Fin}(n+1) \to \mathbb{N}$
satisfying the two properties is equal to $a(n)$.
-/
theorem oeis_A028859_conjecture_1 (n : ℕ) :
  let L := n + 1
  let Sequence := Fin L → ℕ
  let S : Set Sequence :=
    { σ : Sequence |
      L > 0 ∧ -- L = n + 1 ensures this is true for n ≥ 0
      (∀ i : Fin L, σ i > 0) ∧ -- All elements are positive integers
      -- Property 1: Covers initial interval
      let max_val := Finset.sup Finset.univ σ -- max value exists since Fin L is finite and non-empty
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
      -- Property 2: Non-adjacent parts are weakly decreasing
      (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    }
  -- The set S is finite. We state the conjecture as the existence of a finset F
  -- corresponding to S with the correct cardinality, which is the standard way to relate set
  -- size to a natural number when the Fintype instance is not trivial.
  ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a n
:= by sorry
