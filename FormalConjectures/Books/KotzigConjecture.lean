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
# Kotzig's Conjecture

*Reference:* A. Kotzig, cited in A. Rosa, *On certain valuations of the vertices of a graph*,
Theory of Graphs (Internat. Sympos., Rome, 1966), Gordon and Breach, 1967, pp. 349–355.

Kotzig conjectured that for every $n$, the complete graph $K_{2n+1}$ decomposes into copies of
any $n$-edge tree via cyclic shifts of a single embedding. This is strictly stronger than
Ringel's conjecture; see `Books/RingelConjecture.lean`. The large-$n$ case is proved by
Montgomery–Pokrovskiy–Sudakov; see `Arxiv/2001.02665/RingelConjecture.lean`.
-/
namespace KotzigConjecture

open SimpleGraph

/--
For any tree $T$ with $n$ edges, the complete graph $K_{2n+1}$ decomposes into
$2n+1$ edge-disjoint copies of $T$ via cyclic shifts of a single embedding.

The $2n+1$ copies are `f 0, f 1, …, f (2n)` where `f i v = f 0 v + i` for all vertices
$v$ — each copy is obtained by adding $i$ (mod $2n+1$) to every vertex of the base copy.
This is strictly stronger than `RingelConjecture.ringel_conjecture`.
-/
@[category research open, AMS 5]
theorem kotzig_conjecture {V : Type} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (n : ℕ) (hn : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  sorry

end KotzigConjecture
