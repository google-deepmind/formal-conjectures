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
# Written on the Wall II - Conjecture 103

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture103

open Classical SimpleGraph

/-- An induced subgraph is bipartite exactly when its vertices admit a two-coloring. -/
@[category API, AMS 5]
theorem induce_isBipartite_iff_exists_coloring {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

/-- Computable largest induced bipartite subgraph size via powerset enumeration. -/
def computableLargestInducedBipartiteSubgraphSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter fun s : Finset α =>
    ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v).sup Finset.card

/-- The computable largest induced bipartite subgraph size agrees with the `sSup` definition. -/
@[category API, AMS 5]
theorem largestInducedBipartiteSubgraphSize_eq_computable
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.largestInducedBipartiteSubgraphSize = computableLargestInducedBipartiteSubgraphSize G := by
  unfold SimpleGraph.largestInducedBipartiteSubgraphSize
    computableLargestInducedBipartiteSubgraphSize
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨s, hs, rfl⟩
      apply Finset.le_sup
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ s),
        (induce_isBipartite_iff_exists_coloring G s).mp hs⟩
  · apply Finset.sup_le
    intro s hs
    apply le_csSup
    · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨s, (induce_isBipartite_iff_exists_coloring G s).mpr
        (Finset.mem_filter.mp hs).2, rfl⟩

/-- The 11-vertex counterexample: a triangle with four leaves on each of two vertices. -/
abbrev wowii103Counterexample : SimpleGraph (Fin 11) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(0, 2), s(1, 2),
    s(0, 3), s(0, 4), s(0, 5), s(0, 6),
    s(1, 7), s(1, 8), s(1, 9), s(1, 10)
  }

/-- The counterexample is connected. -/
@[category test, AMS 5]
theorem wowii103Counterexample_connected : wowii103Counterexample.Connected := by
  decide +native

/-- The counterexample has independence number nine. -/
@[category test, AMS 5]
theorem wowii103Counterexample_indepNum : wowii103Counterexample.indepNum = 9 := by
  rw [indep_num_eq_computable]
  decide +native

/-- The largest induced bipartite subgraph of the counterexample has ten vertices. -/
@[category test, AMS 5]
theorem wowii103Counterexample_bipartiteSize :
    wowii103Counterexample.largestInducedBipartiteSubgraphSize = 10 := by
  rw [largestInducedBipartiteSubgraphSize_eq_computable]
  decide +native

/-- The counterexample has average eccentricity $30/11$. -/
@[category test, AMS 5]
theorem wowii103Counterexample_averageEccentricity :
    averageEccentricity wowii103Counterexample = 30 / 11 := by
  unfold averageEccentricity
  have hsum : (∑ v : Fin 11, (wowii103Counterexample.eccent v).toNat) = 30 := by
    simp_rw [eccent_eq_computable wowii103Counterexample wowii103Counterexample_connected]
    decide +native
  rw [hsum]
  norm_num

/-- The logarithm of the counterexample's average eccentricity lies strictly between one and two. -/
@[category test, AMS 5]
theorem one_lt_log_thirty_eleven_and_lt_two :
    1 < Real.log (30 / 11 : ℝ) ∧ Real.log (30 / 11 : ℝ) < 2 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  · exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans (by norm_num)

/--
WOWII [Conjecture 103](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\alpha(G) \le \lfloor b(G) - \ln(\mathrm{ecc\_avg}(G)) \rfloor$
where $\alpha(G) = G.\mathrm{indepNum}$ is the independence number,
$b(G)$ is the largest induced bipartite subgraph size, and
$\mathrm{ecc\_avg}(G) = G.\mathrm{averageEccentricity}$ is the average
eccentricity of $G$. Uses `Real.log` (natural logarithm).

This conjecture is false. The graph `wowii103Counterexample` has independence number $9$,
largest induced bipartite subgraph size $10$, and average eccentricity $30/11$. Since
$1 < \ln(30/11) < 2$, the proposed upper bound is $8$.
-/
@[category research solved, AMS 5]
theorem conjecture103 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (G.indepNum : ℝ) ≤ ⌊b G - Real.log (averageEccentricity G)⌋ := by
  show False ↔ _
  rw [false_iff]
  intro h
  have hbad := h (Fin 11) wowii103Counterexample wowii103Counterexample_connected
  rw [wowii103Counterexample_indepNum, b, wowii103Counterexample_bipartiteSize,
    wowii103Counterexample_averageEccentricity] at hbad
  have hfloor : ⌊(10 : ℝ) - Real.log (30 / 11 : ℝ)⌋ = (8 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith [one_lt_log_thirty_eleven_and_lt_two.1,
      one_lt_log_thirty_eleven_and_lt_two.2]
  norm_num [hfloor] at hbad

end WrittenOnTheWallII.GraphConjecture103
