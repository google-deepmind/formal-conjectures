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
# Written on the Wall II - Conjecture 166

*References:*
- [E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), entry 166 (2005).
- [takumayellow/math-autoresearch, Lower bounds for the spanning-tree leaf number (p0010)](https://github.com/takumayellow/math-autoresearch/tree/c24c95c4e0f706f5e236ad6b5bd68ca9a851710c/papers/p0010_wowii_ls_lower_bounds).

For a finite nontrivial connected simple graph $G$, let $L_s(G)$ denote the maximum number of
leaves over all spanning trees of $G$, let $M(G) = \{v \mid \deg_G(v) = \Delta(G)\}$ denote the
set of maximum-degree vertices, and let $N_G(M) \setminus M$ denote the external neighborhood of
$M$ (vertices outside $M$ adjacent to at least one vertex of $M$). Conjecture 166 proposed that
$$L_s(G) \ge \frac{|N_G(M) \setminus M|}{\sqrt{\mathrm{rad}(G)}}.$$

The conjecture is **false**: there is a $20$-vertex connected subcubic graph of radius $5$ in
which $6$ vertices have degree $3$ and all $14$ remaining vertices have degree $2$ and a neighbor
in $M$, so $|N_G(M) \setminus M| = 14$, while two vertex-disjoint $4$-cycles force every spanning
tree to have at most $6$ leaves ($L_s(G) = 6 < 14 / \sqrt{5}$, since $6^2 \cdot 5 = 180 < 196$).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture166

open SimpleGraph

/-- The set $M(G)$ of vertices attaining the maximum degree $\Delta(G)$. -/
def maxDegreeVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = G.maxDegree

/-- The external neighborhood $N_G(M) \setminus M$ of the maximum-degree vertices $M(G)$:
vertices outside $M(G)$ that have at least one neighbor in $M(G)$. -/
def externalMaxDegreeNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun w =>
    w ∉ maxDegreeVertices G ∧ ∃ v ∈ maxDegreeVertices G, G.Adj v w

/--
WOWII [Conjecture 166](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf):
does every finite nontrivial connected simple graph $G$ satisfy
$L_s(G) \ge |N_G(M) \setminus M| / \sqrt{\mathrm{rad}(G)}$,
where $M$ is the set of maximum-degree vertices of $G$?

This is false: a $20$-vertex connected subcubic graph of radius $5$ satisfies
$|N_G(M) \setminus M| = 14$ and $L_s(G) = 6$, whereas $14 / \sqrt{5} > 6$ ($196 > 5 \cdot 36$).
The linked Palomar proof certifies the equivalent squared integer formulation on this graph.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000010"]
theorem conjecture166 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        ((externalMaxDegreeNeighbors G).card : ℝ) / Real.sqrt (G.radius.toNat : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- In $K_3$, every vertex has maximum degree $2$, so $M(K_3)$ has $3$ vertices. -/
@[category test, AMS 5]
example : (maxDegreeVertices (⊤ : SimpleGraph (Fin 3))).card = 3 := by
  decide

/-- Because $K_3$ is regular, $M(K_3) = V$ and its external neighborhood $N(M) \setminus M$ is empty. -/
@[category test, AMS 5]
example : (externalMaxDegreeNeighbors (⊤ : SimpleGraph (Fin 3))).card = 0 := by
  decide

/-- For any graph on $4$ vertices, the external neighborhood has cardinality at most $4$. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    (externalMaxDegreeNeighbors G).card ≤ 4 :=
  (Finset.card_le_univ _).trans (by simp)

end WrittenOnTheWallII.GraphConjecture166
