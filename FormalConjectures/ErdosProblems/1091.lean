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
# Erdős Problem 1091

*References:*
- [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant, *Short proofs in
  combinatorics, probability, and number theory II*. arXiv:2604.06609 (2026).
- [La79] Larson, Jean A., *Some graphs with chromatic number three*. J. Combin. Theory Ser. B
  (1979), 317--322.
- [Vo82] Voss, Heinz-Jürgen, *Graphs having circuits with at least two chords*. J. Combin. Theory
  Ser. B (1982), 264--285.
-/

@[expose] public section

open SimpleGraph Filter

namespace Erdos1091

/-- Two diagonals imply one (special case of `HasOddCycleWithChords.mono`). -/
@[category API, AMS 5]
lemma HasOddCycleWithChords.two_imp_one {V : Type*} {G : SimpleGraph V}
    (h : HasOddCycleWithChords G 2) : HasOddCycleWithChords G 1 :=
  h.mono (by omega)

/-- One diagonal implies a plain odd cycle (`k = 0`). -/
@[category API, AMS 5]
lemma HasOddCycleWithChords.one_imp_zero {V : Type*} {G : SimpleGraph V}
    (h : HasOddCycleWithChords G 1) : HasOddCycleWithChords G 0 :=
  h.mono (by omega)

/--
Let $G$ be a $K_4$-free graph with chromatic number $4$. Must $G$ contain an odd cycle with at
least two diagonals?

The first question was solved in the affirmative by Voss [Vo82].
-/
@[category research solved, AMS 5]
theorem erdos_1091.parts.i : answer(True) ↔
    ∀ {V : Type*} [Finite V] (G : SimpleGraph V),
      G.CliqueFree 4 → G.chromaticNumber = 4 → HasOddCycleWithChords G 2 := by
  sorry

/--
More generally, is there some $f(r)\to \infty$ such that every graph with chromatic number $4$,
in which every subgraph on $\leq r$ vertices has chromatic number $\leq 3$, contains an odd cycle
with at least $f(r)$ diagonals?

An internal OpenAI model (see [APSSV26b]) has provided a negative answer to the second question.
-/
@[category research solved, AMS 5]
theorem erdos_1091.parts.ii : answer(False) ↔
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) {V : Type*} [Finite V] (G : SimpleGraph V),
        G.chromaticNumber = 4 → G.IsLocallyColorable r 3 →
          HasOddCycleWithChords G (f r) := by
  sorry

/--
Erdős originally asked about the existence of just one diagonal, which is true, and was proved by
Larson [La79].
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.one_diagonal {V : Type*} [Finite V] (G : SimpleGraph V)
    (hK : G.CliqueFree 4) (hχ : G.chromaticNumber = 4) :
    HasOddCycleWithChords G 1 := by
  sorry

/--
In fact Larson proved the following stronger conjecture of Bollobás and Erdős: if $G$ is a
$K_4$-free graph containing no odd cycle with a diagonal then either $G$ is bipartite, or $G$
contains a cut vertex, or $G$ contains a vertex with degree $\leq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.bollobas_erdos {V : Type*} [Finite V] (G : SimpleGraph V)
    (hK : G.CliqueFree 4) (h : ¬ HasOddCycleWithChords G 1) :
    G.IsBipartite ∨ (∃ v, G.IsCutVertex v) ∨ (∃ v, (G.neighborSet v).encard ≤ 2) := by
  sorry

/--
The pentagonal wheel shows that three diagonals are not guaranteed.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.three_diagonals :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧ G.chromaticNumber = 4 ∧ ¬ HasOddCycleWithChords G 3 := by
  sorry

/--
An internal OpenAI model (see [APSSV26b]) has provided a negative answer to the second question:
for every $m\geq 1$ there is a graph $G$, with no $K_4$, on $\asymp m$ many vertices with
chromatic number $4$, such that every proper subgraph has chromatic number $\leq 3$, and every
cycle in $G$ contains at most $10$ diagonals.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.counterexample :
    ∃ C : ℕ, ∀ m : ℕ, 1 ≤ m →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        m ≤ n ∧ n ≤ C * m ∧ G.CliqueFree 4 ∧ G.chromaticNumber = 4 ∧
          (∀ H : G.Subgraph, H ≠ ⊤ → H.coe.chromaticNumber ≤ 3) ∧
          (∀ c : G.Cycle, c.chords.encard ≤ 10) := by
  sorry


/-- `C_{n+3}` is bridgeless. -/
@[category API, AMS 5]
theorem erdos_1091.variants.cycleGraph_isBridgeless (n : ℕ) :
    IsBridgeless (cycleGraph (n + 3)) :=
  SimpleGraph.cycleGraph_isBridgeless n

/-- The Eulerian cycle of `C_{n+3}` has no chords. -/
@[category API, AMS 5]
theorem erdos_1091.variants.cycleGraph_chords_eq_empty (n : ℕ) :
    (Cycle.cycleGraph n).chords = ∅ :=
  Cycle.cycleGraph_chords_eq_empty n

/-- `C_{n+3}` is never a forest. -/
@[category test, AMS 5]
theorem erdos_1091.variants.cycleGraph_not_isAcyclic (n : ℕ) :
    ¬ (cycleGraph (n + 3)).IsAcyclic :=
  SimpleGraph.cycleGraph_not_isAcyclic n

/-- Eulerian cycle of `C_{n+3}` has `n+3` edges. -/
@[category API, AMS 5]
theorem erdos_1091.variants.cycleGraph_edges_length (n : ℕ) :
    (Cycle.cycleGraph n).edges.length = n + 3 :=
  Cycle.cycleGraph_edges_length n

/-- Bridgeless graphs are forests iff edgeless. -/
@[category API, AMS 5]
theorem erdos_1091.variants.isBridgeless_edgeFinset_eq_empty_iff_isAcyclic
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IsBridgeless G) : G.edgeFinset = ∅ ↔ G.IsAcyclic :=
  h.edgeFinset_eq_empty_iff_isAcyclic

/-- `K_{n+3}` is bridgeless (every edge lies on a triangle). -/
@[category API, AMS 5]
theorem erdos_1091.variants.completeGraph_isBridgeless (n : ℕ) :
    IsBridgeless (completeGraph (Fin (n + 3))) :=
  SimpleGraph.completeGraph_isBridgeless n

/-- `K_n` (`n ≥ 3`) is bridgeless. -/
@[category API, AMS 5]
theorem erdos_1091.variants.completeGraph_isBridgeless_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    IsBridgeless (completeGraph (Fin n)) :=
  SimpleGraph.completeGraph_isBridgeless_of_three_le hn

/-- `K_{n+3}` has an odd cycle with (at least) `0` chords. -/
@[category API, AMS 5]
theorem erdos_1091.variants.hasOddCycleWithChords_completeGraph_zero (n : ℕ) :
    HasOddCycleWithChords (completeGraph (Fin (n + 3))) 0 :=
  SimpleGraph.hasOddCycleWithChords_completeGraph_zero n

/-- `K_n` (`n ≥ 3`) has an odd cycle with (at least) `0` chords. -/
@[category API, AMS 5]
theorem erdos_1091.variants.hasOddCycleWithChords_completeGraph_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    HasOddCycleWithChords (completeGraph (Fin n)) 0 :=
  SimpleGraph.hasOddCycleWithChords_completeGraph_of_three_le hn

/-- Bundled triangle in `K_{n+3}` has length `3`. -/
@[category API, AMS 5]
theorem erdos_1091.variants.length_completeGraph_triangle (n : ℕ) :
    (Cycle.completeGraph_triangle n).length = 3 :=
  Cycle.length_completeGraph_triangle n

/-- A triangle in `K_{n+3}` has no diagonals. -/
@[category API, AMS 5]
theorem erdos_1091.variants.completeGraph_triangle_chords (n : ℕ) :
    (Cycle.completeGraph_triangle n).chords = ∅ :=
  Cycle.completeGraph_triangle_chords n

end Erdos1091
