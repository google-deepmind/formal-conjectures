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
# Erdős Problem 348

*Reference:* [erdosproblems.com/348](https://www.erdosproblems.com/348)
-/
section Prelims

namespace Function

/--
A sequence of naturals is complete if any positive natural can be written
as a finite sum of distinct values in the sequence.
-/
abbrev IsCompleteNatSeq := fun a => ∀ n > 0,
  ∃ s : Finset ℕ, Set.InjOn a s ∧ s.sum a = n

end Function

end Prelims

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.
-/
@[category research open, AMS 11]
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → (Function.updateFinset a s 0).IsCompleteNatSeq)
        (_ : ∀ t, t.card = n → ¬(Function.updateFinset a t 0).IsCompleteNatSeq) } =
    answer(sorry) := by
  sorry
