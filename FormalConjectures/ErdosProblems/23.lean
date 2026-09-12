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
# Erdős Problem 23

*References:*
* [Cycle plus uniform background weighted special case](https://github.com/SproutSeeds/erdos-problems/blob/68fbae4b2f6eba86f1b28d62b1b370bfabd7d92a/packs/graph-theory/problems/23/publication/cycle-background/PROOF.md)
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
* [Balogh-Clemen-Lidicky, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179)
* [McKay, Extremal graphs for bipartization of triangle-free graphs](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)
-/

open SimpleGraph BigOperators

namespace Erdos23

open scoped Classical in
/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  sorry

open scoped Classical in
/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  sorry

open scoped Classical in
/--
Every triangle-free graph on $25$ vertices can be made bipartite by removing at most $25$
edges.

This is the $n = 5$ case of Erdős Problem 23.  It follows from the high-density range of
Balogh-Clemen-Lidicky together with McKay's complete catalogue of the 23-vertex extremal
graphs for bipartization of triangle-free graphs.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5 :
    ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 25)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  sorry

open scoped Classical in
/--
There exists a triangle-free graph on $25$ vertices such that at least $25$ edges must be
removed to make it bipartite.  The balanced blow-up of $C_5$ with five parts of size $5$
witnesses this.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

open scoped Classical in
/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  sorry

open scoped Classical in
/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

/-- The Clebsch graph, represented by four-bit vertices. -/
def clebschGraph : SimpleGraph (Fin 16) :=
  .fromRel fun u v => u.val ^^^ v.val ∈ ([1, 2, 4, 8, 15] : List ℕ)

/-- Adjacency in the Mycielski lift; `none` is the apex and `true` marks twins. -/
def clebschMycielskiAdj : Option (Fin 16 × Bool) → Option (Fin 16 × Bool) → Prop
  | none, none => False
  | none, some (_, b) => b = true
  | some (_, b), none => b = true
  | some (u, b), some (v, c) => clebschGraph.Adj u v ∧ ¬(b = true ∧ c = true)

/-- The Mycielski lift of the Clebsch graph. -/
def clebschMycielski : SimpleGraph (Option (Fin 16 × Bool)) :=
  .fromRel clebschMycielskiAdj

/-- Background weight $r$, an extra $h$ on the cycle $(0,1,3,7,15)$,
independent twin weights $b$, and apex weight $z$. -/
def cycleBackgroundWeight (r h z : ℝ) (b : Fin 16 → ℝ) :
    Option (Fin 16 × Bool) → ℝ
  | none => z
  | some (v, false) => r + if v ∈ ({0, 1, 3, 7, 15} : Finset (Fin 16)) then h else 0
  | some (v, true) => b v

/-- The apex is adjacent to every twin. -/
@[category test, AMS 5]
theorem clebschMycielski_apex_adj_twin (v : Fin 16) :
    clebschMycielski.Adj none (some (v, true)) := by
  simp [clebschMycielski, clebschMycielskiAdj]

/-- Twins are never adjacent. -/
@[category test, AMS 5]
theorem clebschMycielski_twins_not_adjacent (u v : Fin 16) :
    ¬clebschMycielski.Adj (some (u, true)) (some (v, true)) := by
  simp [clebschMycielski, clebschMycielskiAdj]

/-- Zero parameters give zero vertex weights. -/
@[category test, AMS 5]
theorem cycleBackgroundWeight_zero (v : Option (Fin 16 × Bool)) :
    cycleBackgroundWeight 0 0 0 (fun _ ↦ 0) v = 0 := by
  cases v with
  | none => rfl
  | some p => rcases p with ⟨v, q⟩; cases q <;> simp [cycleBackgroundWeight]

open scoped Classical in
/--
Give every original vertex of the Mycielski lift of the Clebsch graph weight $r$, with
an additional weight $h$ on the cycle $(0,1,3,7,15)$. For all $r,h,z\geq0$ and
arbitrary nonnegative twin weights, a cut leaves monochromatic edge weight at most
$1/25$ of the square of the total vertex weight. The apex has weight $z$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/erdos-problems/blob/68fbae4b2f6eba86f1b28d62b1b370bfabd7d92a/packs/graph-theory/problems/23/publication/cycle-background/P23CycleBackgroundSubmission.lean#L50"]
theorem erdos_23.variants.cycle_background :
    ∀ (r h z : ℝ) (b : Fin 16 → ℝ), 0 ≤ r → 0 ≤ h → 0 ≤ z →
      (∀ v, 0 ≤ b v) → ∃ c : Option (Fin 16 × Bool) → Bool,
        (25 / 2 : ℝ) * (∑ u, ∑ v,
          if clebschMycielski.Adj u v ∧ c u = c v then
            cycleBackgroundWeight r h z b u * cycleBackgroundWeight r h z b v else 0) ≤
          (16 * r + 5 * h + (∑ v, b v) + z) ^ 2 := by sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23
