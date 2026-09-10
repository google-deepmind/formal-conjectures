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
# Erdős Problem 747

*References:*
- [erdosproblems.com/747](https://www.erdosproblems.com/747)
- [JKV08] Johansson, Anders and Kahn, Jeff and Vu, Van, Factors in random graphs. Random Structures
Algorithms (2008), 1-28.
- [Ka23] Kahn, Jeff, Asymptotics for Shamir's problem. Adv. Math. (2023), Paper No. 109019, 39.
-/

namespace Erdos747

open Filter Asymptotics
open scoped Topology

/--
How large should $\ell(n)$ be such that, almost surely, a random $3$-uniform hypergraph on $3n$
vertices with $\ell(n)$ edges must contain $n$ vertex-disjoint edges?

The precise asymptotic was given by Kahn [Ka23], proving that the threshold is $\sim n\log n$ (also
for the general problem over $r$-uniform hypergraphs).
-/
@[category research solved, AMS 5 60]
theorem erdos_747 :
    let threshold : ℕ → ℝ := answer(fun n : ℕ ↦ n * Real.log n)
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    Tendsto (fun n ↦ Hypergraph.matchingProbability (3 * n) 3
      ⌊(1 + ε) * threshold n⌋₊ n) atTop (𝓝 1) ∧
    Tendsto (fun n ↦ Hypergraph.matchingProbability (3 * n) 3
      ⌊(1 - ε) * threshold n⌋₊ n) atTop (𝓝 0) := by
  sorry

end Erdos747
