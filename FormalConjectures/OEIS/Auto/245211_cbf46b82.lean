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

open Nat Finset

/--
A245211: $a(n) = \sum_{d \mid n, d < n} (d \cdot \tau(d))$, where $\tau(d)$ is the number of divisors of $d$.
It is computed as $\left(\sum_{d \mid n} d \cdot \tau(d)\right) - n \cdot \tau(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

/-- A245211 Conjecture: 21 is only number such that a(n) = n. -/
theorem oeis_245211_conjecture_0 : ∀ n : ℕ, 0 < n → (a n = n ↔ n = 21) := by
  sorry
