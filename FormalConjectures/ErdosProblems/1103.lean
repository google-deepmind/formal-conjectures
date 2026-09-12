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
# Erdős Problem 1103

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
-/

open Filter Set
open scoped Topology

namespace Erdos1103

/-- Every sum of two (not necessarily distinct) elements of `A` is squarefree. -/
def SquarefreeSumset (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)

/-- Increasing enumeration of an infinite set of naturals. -/
noncomputable def enum (A : Set ℕ) (n : ℕ) : ℕ := Nat.nth (· ∈ A) n

/--
Let $A$ be an infinite sequence of integers such that every $n\in A+A$ is squarefree. How fast
must $A$ grow?

In particular, is there such an infinite $A$ of polynomial growth?
-/
@[category research open, AMS 11]
theorem erdos_1103 :
    answer(sorry) ↔
      ∃ A : Set ℕ, A.Infinite ∧ SquarefreeSumset A ∧
        ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
          ∀ n : ℕ, (enum A n : ℝ) ≤ C * (n : ℝ) ^ k := by
  sorry

/--
Erdős notes there exists such a sequence which grows exponentially.
-/
@[category research solved, AMS 11]
theorem erdos_1103.variants.exponential :
    ∃ A : Set ℕ, A.Infinite ∧ SquarefreeSumset A ∧
      ∃ C > (1 : ℝ), ∀ n : ℕ, (n : ℝ) ≤ C ^ (enum A n) := by
  sorry

end Erdos1103
