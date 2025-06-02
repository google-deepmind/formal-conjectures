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
# Erdős Problem 412

*Reference:* [erdosproblems.com/412](https://www.erdosproblems.com/412)

Reviewed by @b-mehta on 2025-05-27
-/
open ArithmeticFunction

/--
Let $σ_1(n)=σ(n)$, the sum of divisors function, and $σ_k(n) = σ(σ_{k−1}(n))$.
Is it true that, for every $m, n ≥ 2$, there exist some $i, j$ such that $σ_i(m) = σ_j(n)$?
-/
@[category research open, AMS 11]
theorem erdos_412 : (∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n) ↔ answer(sorry) := by
  sorry
