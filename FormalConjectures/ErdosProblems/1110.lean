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
import FormalConjectures.ErdosProblems.«246»

/-!
# Erdős Problem 1110

*Reference:* [Erdős Problem 1110](https://www.erdosproblems.com/1110)
-/

namespace Erdos1110

/--
$n$ is representable with respect to $p$ and $q$ if it is the sum of a finite
divisibility antichain of terms of the form $p^kq^l$.
-/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ Erdos246.Gamma p q ∧
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧
    s.sum id = n

/--
Let $p>q\geq 2$ be two coprime integers. We call $n$ representable if it is the sum of
integers of the form $p^kq^l$, none of which divide each other.

If $\{p,q\}\neq \{2,3\}$ then what can be said about the density of non-representable
numbers? Are there infinitely many coprime non-representable numbers?
-/
@[category research open, AMS 5 11]
theorem erdos_1110 :
    answer(sorry) ↔ ∀ (p q : ℕ), q < p → 2 ≤ q →
      Nat.Coprime p q → ¬(p = 3 ∧ q = 2) →
      Set.Infinite {n : ℕ | Nat.Coprime n (p * q) ∧ ¬Representable p q n} := by
  sorry

end Erdos1110
