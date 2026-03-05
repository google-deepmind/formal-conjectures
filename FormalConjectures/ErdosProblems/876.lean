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
# Erdős Problem 876

*Reference:* [erdosproblems.com/876](https://www.erdosproblems.com/876)
-/

namespace Erdos876

/--
A set $A \subseteq \mathbb{N}$ is sum-free in the sense of Erdős if no element of $A$ can be
expressed as the sum of finitely many distinct smaller elements of $A$.
-/
def IsSumFreeErdos (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → (∀ x ∈ S, x ∈ A) → (∀ x ∈ S, x < a) → S.sum id ≠ a

/--
Let $A = \{a_1 < a_2 < \cdots\} \subseteq \mathbb{N}$ be an infinite sum-free set (no element
is the sum of finitely many distinct smaller elements of $A$). Is it possible that
$a_{n+1} - a_n < n$ for all sufficiently large $n$?

Erdős notes that Graham proved there exists such a sequence with
$a_{n+1} - a_n < n^{1+o(1)}$.
-/
@[category research open, AMS 5 11]
theorem erdos_876 : answer(sorry) ↔
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsSumFreeErdos (Set.range a) ∧
      ∃ N, ∀ n ≥ N, a (n + 1) - a n < n + 1 := by
  sorry

end Erdos876
