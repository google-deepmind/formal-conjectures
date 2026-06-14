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
# Ringel's Conjecture

*Reference:* G. Ringel, *Problem 25*, in *Theory of Graphs and its Applications*
(Proc. Sympos. Smolenice, 1963), Academia, Prague, 1964.

Ringel's conjecture (1963): the complete graph $K_{2n+1}$ decomposes into copies of any tree
with $n$ edges. It remains open; the case of all sufficiently large $n$ is proved by
Montgomery–Pokrovskiy–Sudakov, see `Arxiv/2001.02665/RingelConjecture.lean`.
-/
namespace RingelConjecture

open SimpleGraph

/--
For any tree $T$ with $n$ edges, the complete graph $K_{2n+1}$ decomposes into
$2n+1$ edge-disjoint copies of $T$.

A "copy" of $T$ is the image `T.map (f i)` of $T$ under a vertex embedding
`f i : V ↪ Fin (2 * n + 1)`; the copies are pairwise edge-disjoint (`Pairwise ... Disjoint`)
and together cover every edge of $K_{2n+1}$ (`⨆ i, T.map (f i) = ⊤`).
-/
@[category research open, AMS 5]
theorem ringel_conjecture {V : Type} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (n : ℕ) (hn : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  sorry

end RingelConjecture
