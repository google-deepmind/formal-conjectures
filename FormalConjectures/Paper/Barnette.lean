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
module

public import FormalConjecturesUtil

/-!
# Barnette's Hamiltonian-cycle conjecture

*Reference:* OpenAI, *Paired states and Hamiltonian cycles in cubic bipartite
planar graphs* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/paper.pdf
-/

@[expose] public section

namespace Barnette

/-- Every finite cubic bipartite planar graph that remains connected after deleting
at most two vertices has a Hamiltonian cycle. The order is at least four, as required
for three-vertex-connectivity. -/
@[category research solved, AMS 5]
theorem hamiltonian_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hregular : G.IsRegularOfDegree 3)
    (hbipartite : G.IsBipartite) (hplanar : Nonempty G.PlaneEmbedding)
    (hcard : 4 ≤ Fintype.card V)
    (hconnected : ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  sorry

end Barnette
