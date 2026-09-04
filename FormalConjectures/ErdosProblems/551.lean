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
# Erdős Problem 551

*Reference:* [erdosproblems.com/551](https://www.erdosproblems.com/551)

-/

open SimpleGraph

namespace Erdos551

/--
Prove that $$R(C_k,K_n)=(k-1)(n-1)+1$$ for $k\geq n\geq 3$ (except when $n=k=3$).

Here $R(C_k, K_n)$ is `ramseyNumber (cycleGraph k) (completeGraph (Fin n))`: the least $N$ such that
every `SimpleGraph (Fin N)` (the "red" graph of a two-colouring of $K_N$) contains a red $C_k$ or a
blue $K_n$ (a copy of `completeGraph (Fin n)` in its complement).
-/
@[category research open, AMS 5]
theorem erdos_551 (k n : ℕ) (hn : 3 ≤ n) (hkn : n ≤ k) (hne : (k, n) ≠ (3, 3)) :
    ramseyNumber (cycleGraph k) (completeGraph (Fin n)) = (k - 1) * (n - 1) + 1 := by
  sorry

/-- Sanity check: the defining set of $R(C_k, K_n)$ is upward closed, specialising the general
`SimpleGraph.ramseyNumber_setOf_upward_closed`. -/
@[category test, AMS 5]
theorem ramseyCycleClique_setOf_upward_closed (k n : ℕ) :
    ∀ N ∈ {N : ℕ | ∀ F : SimpleGraph (Fin N),
        cycleGraph k ⊑ F ∨ completeGraph (Fin n) ⊑ Fᶜ},
      ∀ N', N ≤ N' → N' ∈ {N : ℕ | ∀ F : SimpleGraph (Fin N),
        cycleGraph k ⊑ F ∨ completeGraph (Fin n) ⊑ Fᶜ} :=
  ramseyNumber_setOf_upward_closed (cycleGraph k) (completeGraph (Fin n))

end Erdos551
