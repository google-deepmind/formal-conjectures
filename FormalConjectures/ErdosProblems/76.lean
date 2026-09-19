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
# Erdős Problem 76

*References:*
- [erdosproblems.com/76](https://www.erdosproblems.com/76)
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math. (1997),
  81-85.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
- [GrLe20] Gruslys, V. and Letzter, S., *Monochromatic triangle packings in red-blue graphs*.
  arXiv:2008.05311 (2020).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos76

/-- A family of triangles (`3`-sets of vertices) is *edge-disjoint* if any two distinct members
share at most one vertex. -/
def EdgeDisjoint {V : Type*} [DecidableEq V] (P : Finset (Finset V)) : Prop :=
  ∀ s ∈ P, ∀ t ∈ P, s ≠ t → (s ∩ t).card ≤ 1

/--
Is it true that in any $2$-colouring of the edges of $K_n$ there must exist at least
$$(1+o(1))\frac{n^2}{12}$$
many edge-disjoint monochromatic triangles?

Conjectured by Erdős, Faudree, and Ordman. This would be best possible, as witnessed by dividing
the vertices of $K_n$ into two equal parts and colouring all edges between the parts red and all
edges inside the parts blue.

The answer is yes, proved by Gruslys and Letzter [GrLe20].

A $2$-colouring of the edges of $K_n$ is encoded by the graph $G$ of red edges, whose complement
is the graph of blue edges.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos76.lean#L58"]
theorem erdos_76 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), ∃ P : Finset (Finset (Fin n)),
      (∀ t ∈ P, G.IsNClique 3 t ∨ Gᶜ.IsNClique 3 t) ∧ EdgeDisjoint P ∧
        (1 - ε) * n ^ 2 / 12 ≤ P.card := by
  sorry

/--
In [Er97d] Erdős also asks for a lower bound for the count of edge-disjoint monochromatic
triangles in a single colour (the colour chosen to maximise this quantity), and speculates that
the answer is $\geq cn^2$ for some constant $c>1/24$.
-/
@[category research open, AMS 5]
theorem erdos_76.variants.single_colour : answer(sorry) ↔ ∃ c : ℝ, 1 / 24 < c ∧
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), ∃ P : Finset (Finset (Fin n)),
      ((∀ t ∈ P, G.IsNClique 3 t) ∨ (∀ t ∈ P, Gᶜ.IsNClique 3 t)) ∧ EdgeDisjoint P ∧
        c * n ^ 2 ≤ P.card := by
  sorry

end Erdos76
