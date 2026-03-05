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
# Erdős Problem 207

*Reference:* [erdosproblems.com/207](https://www.erdosproblems.com/207)

For any $g \geq 2$, if $n$ is sufficiently large and $n \equiv 1, 3 \pmod{6}$, then there
exists a Steiner triple system on $n$ vertices with girth greater than $g$ — that is,
a $3$-uniform hypergraph where every pair of vertices is in exactly one edge, and
any $j$ edges (for $2 \leq j \leq g$) span at least $j + 3$ vertices.

The congruence condition $n \equiv 1, 3 \pmod{6}$ is the necessary and sufficient
divisibility condition for a Steiner triple system on $n$ points to exist.

[KSSS22b] Kwan, M., Sah, A., Sawhney, M., and Simkin, M., _High-girth Steiner
triple systems_ (2022).
-/

namespace Erdos207

/-- A set of hyperedges forms a Steiner triple system: each edge has exactly $3$
    vertices, and every pair of distinct vertices appears in exactly one edge. -/
def IsSteinerTripleSystem {n : ℕ} (edges : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ edges, e.card = 3) ∧
  (∀ u v : Fin n, u ≠ v → ∃! e, e ∈ edges ∧ u ∈ e ∧ v ∈ e)

/--
Erdős Problem 207 [KSSS22b]:

For any $g \geq 2$, if $n$ is sufficiently large and $n \equiv 1$ or $3 \pmod{6}$, there exists
a Steiner triple system on $n$ vertices such that any $j$ edges (for $2 \leq j \leq g$)
span at least $j + 3$ vertices.

The girth condition forbids short "cycles" in the hypergraph: any collection of
$j$ edges (for $2 \leq j \leq g$) must contain at least $j + 3$ distinct vertices.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].
-/
@[category research solved, AMS 5]
theorem erdos_207 :
    ∀ g : ℕ, 2 ≤ g →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (n % 6 = 1 ∨ n % 6 = 3) →
          ∃ edges : Finset (Finset (Fin n)),
            IsSteinerTripleSystem edges ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ g →
              ∀ S : Finset (Finset (Fin n)), S ⊆ edges → S.card = j →
                j + 3 ≤ (S.biUnion id).card := by
  sorry

end Erdos207
