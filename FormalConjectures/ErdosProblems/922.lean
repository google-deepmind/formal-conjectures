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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 922

*References:*
- [erdosproblems.com/922](https://www.erdosproblems.com/922)
- [ErHa67b] Erdős, P. and Hajnal, András, *On chromatic graphs*. Mat. Lapok (1967), 1-4.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Fo70b] Folkman, J. H., *An upper bound on the chromatic number of a graph*. (1970), 437-457.
-/

@[expose] public section

open SimpleGraph

namespace Erdos922

/--
Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size
$\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ have chromatic number at most
$k+2$?

A question of Erdős and Hajnal [ErHa67b]. The case $k=0$ is trivial, but they could not prove
this even for $k=1$.

This is true, and was proved by Folkman [Fo70b].

See also [73](https://www.erdosproblems.com/73).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos922.lean#L5595"]
theorem erdos_922 : answer(True) ↔ ∀ (k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    (∀ S : Finset V, ∃ I : Finset V, I ⊆ S ∧ (G.induce (I : Set V)).edgeSet = ∅ ∧
      (I.card : ℝ) ≥ (S.card - k : ℝ) / 2) →
    G.chromaticNumber ≤ k + 2 := by
  sorry

end Erdos922
