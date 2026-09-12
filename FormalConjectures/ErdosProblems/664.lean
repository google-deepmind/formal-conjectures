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
# Erdős Problem 664

*References:*
- [erdosproblems.com/664](https://www.erdosproblems.com/664)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
-/

namespace Erdos664

open Filter Asymptotics

/--
Let $0<c<1$ be some constant and $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ be such that $\lvert
A_i\rvert >c\sqrt{n}$ for all $i$ and $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$. Must there
exist some set $B$ such that $B\cap A_i\neq \emptyset$ and $\lvert B\cap A_i\rvert \ll_c 1$ for all
$i$?

Alon has proved that the answer is no.
-/
@[category research solved, AMS 5]
theorem erdos_664 :
    answer(False) ↔ ∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℕ,
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, c * Real.sqrt n < e.card) → H.IsLinearHypergraph →
      ∃ B : Finset (Fin n), ∀ e ∈ H, (B ∩ e).Nonempty ∧ (B ∩ e).card ≤ K := by
  sorry

end Erdos664
