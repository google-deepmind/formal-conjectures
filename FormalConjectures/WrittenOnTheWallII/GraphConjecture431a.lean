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
# Written on the Wall II - Conjecture 431a

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [S. Dubey, Codex Worklog (2026)](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa)
  gives the first public counterexample: $K_{5,5,5}$ with one pendant vertex.
- [AI Village, Graffiti verification worklog, §7ay (2026)](https://gitlab.com/ai-village-agents/village/graffiti-verification)
  shows that `I?bnVrwyW` is the unique counterexample of minimum order.
- [A. Manrique de Lara Martín, On Graffiti.pc Conjectures 431a, 431b and 431c (2026)](https://doi.org/10.5281/zenodo.24558425)
  bounds the residue of an infinite family of counterexamples and formalizes the disproof.

The conjecture is false. The smallest counterexample is the graph with graph6 code `I?bnVrwyW`.
It has ten vertices and the adjacency lists

`0: 4 5 6 7 8 9`, `1: 5 6 7 8 9`, `2: 5 6 7 8 9`, `3: 7 8`, `4: 0 5 6 7 8 9`,
`5: 0 1 2 4`, `6: 0 1 2 4`, `7: 0 1 2 3 4 9`, `8: 0 1 2 3 4 9`, `9: 0 1 2 4 7 8`.

Vertex `3` is the only vertex of degree two, so $N(D) = \{7, 8\}$. No vertex outside
$\{7, 8\}$ has exactly one neighbor in it, so $\mathrm{peN}(N(D)) = 0$. The residue is two.
Vertex `3` is the only vertex that lies in no triangle, so $|T_{\min}(G)| = 1$.
The independent domination number is four, for example with $\{0, 1, 2, 3\}$.
The claimed inequality therefore becomes $4 \le 2 + 0 + 1$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture431a

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set of vertices of degree two. -/
def degreeTwoVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 2

/-- DeLaViña's `N(S)`: the union of open vertex neighborhoods. This may
intersect `S`. -/
def setNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ S, G.Adj u v

/-- DeLaViña's `peN(S)`: the number of vertices outside `S` that have exactly one
neighbor in `S`. -/
def privateExternalNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  (Finset.univ.filter fun v => v ∉ S ∧ (S.filter (G.Adj v)).card = 1).card

/-- `Tmin(G)`: the minimum of the number of triangles containing `v`, over all
vertices `v`. -/
noncomputable def minTrianglesAtVertex [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (numTrianglesAtVertex G)

/-- The number of vertices `v` whose number of triangles is `Tmin(G)`. -/
noncomputable def freqMinTriangles [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun v => numTrianglesAtVertex G v = minTrianglesAtVertex G).card

set_option linter.style.formal_proof_palomar false in
/--
WOWII [Conjecture 431a](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
asked whether every connected graph $G$ on $n > 3$ vertices satisfies
$i(G) \le \mathrm{residue}(G) + \mathrm{peN}(N(D)) + |T_{\min}(G)|$,
where $D$ is the set of vertices of degree two of $G$.

Here $i(G)$ is the independent domination number and $\mathrm{residue}(G)$ is the
Havel-Hakimi residue. $N(S)$ is the set of vertices adjacent to at least one vertex of
$S$, and $\mathrm{peN}(S)$ is the number of vertices outside $S$ with exactly one neighbor
in $S$. $T(v)$ is the number of triangles that contain $v$, and $T_{\min}(G)$ is the
smallest value of $T(v)$.

The source defines $T_{\min}$ as a number. We read $|T_{\min}(G)|$ as the number of
vertices $v$ with $T(v) = T_{\min}(G)$. The variant
`conjecture431a.variants.min_value` uses the value $T_{\min}(G)$ itself.

The answer is no. The graph `I?bnVrwyW` gives $4 \le 2 + 0 + 1$.
-/
@[category research solved, question, AMS 5,
  formal_proof using lean4 at "https://zenodo.org/records/24559666/files/GraphConjecture431aDisproof.lean"]
theorem conjecture431a :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        G.indepDominationNumber ≤
          residue G + privateExternalNeighborCount G (setNeighborhood G (degreeTwoVertices G)) +
            freqMinTriangles G := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
WOWII Conjecture 431a with $|T_{\min}(G)|$ read as the value $T_{\min}(G)$, the smallest
number of triangles that contain a vertex:
$i(G) \le \mathrm{residue}(G) + \mathrm{peN}(N(D)) + T_{\min}(G)$.

This reading already fails on six vertices. Attach a pendant vertex to a vertex of the
part of size three of $K_{2,3}$. The result has $i(G) = 3$, but the bound is $2 + 0 + 0$.
The graph `I?bnVrwyW` also refutes this reading, with $4 \le 2 + 0 + 0$.
-/
@[category research solved, question, AMS 5,
  formal_proof using lean4 at "https://zenodo.org/records/24559666/files/GraphConjecture431aDisproof.lean"]
theorem conjecture431a.variants.min_value :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        G.indepDominationNumber ≤
          residue G + privateExternalNeighborCount G (setNeighborhood G (degreeTwoVertices G)) +
            minTrianglesAtVertex G := by
  sorry

-- Sanity checks

/-- In the path $0 - 1 - 2$, only the middle vertex has degree two. -/
@[category test, AMS 5]
example : degreeTwoVertices
    (SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)} : SimpleGraph (Fin 3)) = {1} := by
  decide

/-- In the path $0 - 1 - 2$, $N(\{1\}) = \{0, 2\}$. -/
@[category test, AMS 5]
example : setNeighborhood
    (SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)} : SimpleGraph (Fin 3)) {1} = {0, 2} := by
  decide

/-- In the path $0 - 1 - 2$, both end vertices have exactly one neighbor in $\{1\}$. -/
@[category test, AMS 5]
example : privateExternalNeighborCount
    (SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)} : SimpleGraph (Fin 3)) {1} = 2 := by
  decide

/-- In $K_3$, every vertex lies in one triangle, so all three vertices attain the minimum. -/
@[category test, AMS 5]
example : freqMinTriangles (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold freqMinTriangles minTrianglesAtVertex numTrianglesAtVertex
  decide

end WrittenOnTheWallII.GraphConjecture431a
