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
# Erdős Problem 924

*References:*
- [erdosproblems.com/924](https://www.erdosproblems.com/924)
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Er75b] Erdős, Paul, _Problems and results in combinatorial number theory_. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [Fo70] Folkman, Jon, _Graphs with monochromatic complete subgraphs in every edge coloring_.
  SIAM J. Appl. Math. (1970), 19-24.
- [NeRo76] Nešetřil, Jaroslav and Rödl, Vojtěch, _The Ramsey property for graphs with forbidden
  complete subgraphs_. J. Combinatorial Theory Ser. B (1976), 243--249.
-/

@[expose] public section

namespace Erdos924

/-- A graph `G` is *edge-Ramsey for `K_l` with `k` colours* (in arrow notation,
$G \to (K_l)^e_k$) if every $k$-colouring of the edges of `G` contains a monochromatic copy of
$K_l$. -/
def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ c : G.edgeSet → Fin k, ∃ i : Fin k, ∃ S : Finset V, S.card = l ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = i

/--
Let $k\geq 2$ and $l\geq 3$. Is there a graph $G$ which contains no $K_{l+1}$ such that every
$k$-colouring of the edges of $G$ contains a monochromatic copy of $K_l$?

A question of Erdős and Hajnal. Folkman [Fo70] proved this when $k=2$. The case for general $k$
was proved by Nešetřil and Rödl [NeRo76].

See [582](https://www.erdosproblems.com/582) for a special case.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos924.lean#L1306"]
theorem erdos_924 : answer(True) ↔ ∀ k ≥ 2, ∀ l ≥ 3,
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  sorry

end Erdos924
