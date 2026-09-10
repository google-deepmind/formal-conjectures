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
# Erdős Problem 207

*References:*
- [erdosproblems.com/207](https://www.erdosproblems.com/207)
- [KSSS22b] Kwan, M. and Sah, A. and Sawhney, M. and Simkin, M., High-girth Steiner triple systems.
arXiv:2201.04554 (2022).
-/

namespace Erdos207

open Filter Asymptotics

/--
For any $g\geq 2$, if $n$ is sufficiently large and $\equiv 1,3\pmod{6}$ then there exists a
3-uniform hypergraph on $n$ vertices such that

- every pair of vertices is contained in exactly one edge (i.e. the graph is a Steiner triple
system) and

- for any $2\leq j\leq g$ any collection of $j$ edges contains at least $j+3$ vertices.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].
-/
@[category research solved, AMS 5]
theorem erdos_207 :
    ∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in atTop,
    n % 6 = 1 ∨ n % 6 = 3 → ∃ H : Finset (Finset (Fin n)),
      H.IsBlockDesign 2 3 ∧ ∀ E ⊆ H,
        2 ≤ E.card → E.card ≤ g → E.card + 3 ≤ (E.biUnion id).card := by
  sorry

end Erdos207
