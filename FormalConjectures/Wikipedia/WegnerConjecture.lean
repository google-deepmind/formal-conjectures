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
# Wegner's conjecture on coloring squares of planar graphs

The square $G^2$ (`SimpleGraph.graphSquare`) of a simple graph $G$ joins distinct vertices at
distance at most $2$ in $G$. Wegner (1977) conjectured that for every finite planar simple graph
$G$ of maximum degree $\Delta \ge 3$, its square $G^2$ is properly colorable with at most $7$
colors when $\Delta = 3$, at most $\Delta + 5$ colors when $4 \le \Delta \le 7$, and at most
$\lfloor 3\Delta / 2 \rfloor + 1$ colors when $\Delta \ge 8$. Thomassen (2018; independently
Hartke, Jahanbekam, and Thomas) proved the subcubic case $\Delta \le 3$, while $\Delta \ge 4$
remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Graph_power)
- [We77] Wegner, G. (1977). *Graphs with given diameter and a coloring problem*, Technical Report,
  University of Dortmund.
- [Th18] Thomassen, C. (2018). *The square of a planar cubic graph is 7-colorable*, J. Combin.
  Theory Ser. B 128, 192--218.
-/

@[expose] public section

namespace WegnerConjecture

/-- Wegner's conjectured color bound as a function of maximum degree `d`. -/
def wegnerColorBound (d : ℕ) : ℕ :=
  if d ≤ 3 then 7 else if d ≤ 7 then d + 5 else 3 * d / 2 + 1

/-- Wegner's color bound is always at least $7$. -/
@[category API, AMS 5]
theorem seven_le_wegnerColorBound (d : ℕ) : 7 ≤ wegnerColorBound d := by
  unfold wegnerColorBound
  split_ifs <;> omega

/-- Evaluates `wegnerColorBound` across Wegner's three degree regimes ($\Delta = 3, 4, 8$). -/
@[category test, AMS 5]
theorem wegnerColorBound_sample_values :
    wegnerColorBound 3 = 7 ∧ wegnerColorBound 4 = 9 ∧ wegnerColorBound 8 = 13 := by
  decide

/-- Because `SimpleGraph.graphSquare` uses extended distance `edist`, the square of an edgeless
graph is edgeless. -/
@[category test, AMS 5]
theorem graphSquare_bot (V : Type*) : (⊥ : SimpleGraph V).graphSquare = ⊥ := by
  ext u v
  simp only [SimpleGraph.graphSquare, SimpleGraph.bot_adj, iff_false, not_and]
  intro huv
  rw [SimpleGraph.edist_bot_of_ne huv]
  simp

/-- The tetrahedral graph $K_4$ is planar with $\Delta(K_4) = 3$, and its square is
$7$-colorable. -/
@[category test, AMS 5]
theorem completeGraph_four_planar_and_square_seven_colorable :
    (SimpleGraph.completeGraph (Fin 4)).IsPlanar ∧
      (SimpleGraph.completeGraph (Fin 4)).maxDegree = 3 ∧
      (SimpleGraph.completeGraph (Fin 4)).graphSquare.Colorable 7 := by
  refine ⟨SimpleGraph.isPlanar_of_card_le_four _ (by simp), by decide, ?_⟩
  refine ⟨SimpleGraph.Coloring.mk (fun v : Fin 4 => (⟨v.1, by omega⟩ : Fin 7)) ?_⟩
  intro u v huv heq
  exact ((SimpleGraph.completeGraph (Fin 4)).graphSquare.ne_of_adj huv)
    (Fin.ext (congrArg (Fin.val : Fin 7 → ℕ) heq))

/--
**Wegner's conjecture** [We77]: for every finite planar simple graph $G$ with $\Delta(G) \ge 3$,
its square `G.graphSquare` is properly colorable with `wegnerColorBound G.maxDegree` colors.
-/
@[category research open, AMS 5]
theorem wegner_conjecture {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsPlanar) (hd : 3 ≤ G.maxDegree) :
    G.graphSquare.Colorable (wegnerColorBound G.maxDegree) := by
  sorry

/--
**Thomassen's theorem** [Th18]: for every finite planar simple graph $G$ with $\Delta(G) \le 3$,
its square `G.graphSquare` is $7$-colorable.
-/
@[category research solved, AMS 5]
theorem wegner_conjecture.variants.subcubic {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsPlanar) (hd : G.maxDegree ≤ 3) :
    G.graphSquare.Colorable 7 := by
  sorry

end WegnerConjecture
