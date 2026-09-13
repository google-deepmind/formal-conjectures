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
# Erdős Problem 894

*Reference:* [erdosproblems.com/894](https://www.erdosproblems.com/894)
-/

namespace Erdos894

/-- A sequence is lacunary if consecutive terms grow by a factor $1+\varepsilon$. -/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ k : ℕ,
    let n := Nat.nth (· ∈ A) k
    let m := Nat.nth (· ∈ A) (k + 1)
    (m : ℝ) ≥ (1 + ε) * n

/--
Let $A=\{n_1<n_2<\cdots\}\subset \mathbb{N}$ be a lacunary sequence (so there exists some
$\epsilon>0$ with $n_{k+1}\geq (1+\epsilon)n_k$ for all $k$). Is it true that there must exist a
finite colouring of $\mathbb{N}$ with no monochromatic solutions to $a-b\in A$?
-/
@[category research open, AMS 5 11]
theorem erdos_894 :
    answer(sorry) ↔
      ∀ A : Set ℕ, A.Infinite ∧ IsLacunary A →
        ∃ n : ℕ, ∃ c : ℕ → Fin n,
          ∀ a b : ℕ, a > b → c a = c b → a - b ∉ A := by
  sorry

end Erdos894
