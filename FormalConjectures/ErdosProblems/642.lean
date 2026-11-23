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
# Erdős Problem 642

*References:*
- [erdosproblems.com/642](https://www.erdosproblems.com/642)
- [CES96] Chen, Guantao and Erdős, Paul and Staton, William, *Proof of a conjecture of Bollobás
  on nested cycles*. J. Combin. Theory Ser. B (1996), 38--43.
- [DMMS24] Draganić, Nemanja and Methuku, Abhishek and Munhá Correia, David and Sudakov,
  Benny, *Cycles with many chords*. Random Structures Algorithms (2024), 3--16.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81-85.
-/

@[expose] public section

open Filter

namespace Erdos642

/-- Every cycle of the graph `G` has more vertices than chords.

A cycle is a closed walk `c` with `c.IsCycle`. It has `c.length` vertices. A chord of `c` is an
edge of `G` between two vertices of `c` that is not an edge of `c`
(`SimpleGraph.Walk.IsChord`). -/
def CyclesHaveMoreVerticesThanChords {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length

open scoped Classical in
/-- The maximal number $f(n)$ of edges of a graph on `n` vertices in which every cycle has more
vertices than chords. There are finitely many graphs on `Fin n`, so the supremum is a maximum. -/
noncomputable def maxEdges (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => CyclesHaveMoreVerticesThanChords G).sup
    fun G => G.edgeSet.ncard

/--
Let $f(n)$ be the maximal number of edges in a graph on $n$ vertices such that all cycles have more
vertices than chords. Is it true that $f(n)\ll n$?

A problem of Hamburger and Szegedy. A chord is an edge between two vertices of the cycle which are
not consecutive in the cycle.
-/
@[category research open, question, AMS 5]
theorem erdos_642 :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- Chen, Erdős, and Staton [CES96] proved $f(n) \ll n^{3/2}$. -/
@[category research solved, AMS 5]
theorem erdos_642.variants.upper_bound_n_pow_three_halves :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
Draganić, Methuku, Munhá Correia, and Sudakov [DMMS24] have improved this to
$$f(n) \ll n(\log n)^8.$$
-/
@[category research solved, AMS 5]
theorem erdos_642.variants.upper_bound_n_log_pow_eight :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n ^ 8) := by
  sorry

/-- A graph without cycles satisfies the condition, since there is no cycle to check. -/
@[category test, AMS 5]
theorem cyclesHaveMoreVerticesThanChords_of_isAcyclic {V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) : CyclesHaveMoreVerticesThanChords G :=
  fun _ c hc => absurd hc (hG c)

open scoped Classical in
/-- Every graph on `n` vertices in which every cycle has more vertices than chords has at most
`maxEdges n` edges. -/
@[category API, AMS 5]
theorem le_maxEdges {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : CyclesHaveMoreVerticesThanChords G) : G.edgeSet.ncard ≤ maxEdges n := by
  unfold maxEdges
  exact Finset.le_sup (f := fun H : SimpleGraph (Fin n) => H.edgeSet.ncard)
    (Finset.mem_filter.2 ⟨Finset.mem_univ G, hG⟩)

/-- The maximum defining $f(n)$ is attained by an admissible graph. -/
@[category API, AMS 5]
theorem exists_maxEdges (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), CyclesHaveMoreVerticesThanChords G ∧
      G.edgeSet.ncard = maxEdges n := by
  classical
  have hne : (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
      CyclesHaveMoreVerticesThanChords G).Nonempty := by
    refine ⟨⊥, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    exact cyclesHaveMoreVerticesThanChords_of_isAcyclic SimpleGraph.isAcyclic_bot
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun G => G.edgeSet.ncard)
  exact ⟨G, (Finset.mem_filter.1 hG).2, hmax.symm⟩

/-- The elementary bound $f(n)\leq\binom n2$. -/
@[category API, AMS 5]
theorem maxEdges_le_choose_two (n : ℕ) : maxEdges n ≤ n.choose 2 := by
  classical
  obtain ⟨G, _, hG⟩ := exists_maxEdges n
  rw [← hG]
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card', Fintype.card_fin] using
    G.card_edgeFinset_le_card_choose_two

/-- There are no edges on an empty vertex set. -/
@[category test, AMS 5]
theorem maxEdges_zero : maxEdges 0 = 0 := by
  have := maxEdges_le_choose_two 0
  simpa using this

/-- The asymptotic question is equivalent to a uniform linear edge bound for every admissible
finite graph, including the empty graph. -/
@[category API, AMS 5]
theorem isBigO_iff_uniform_edge_bound :
    ((fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ))) ↔
      ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        CyclesHaveMoreVerticesThanChords G → (G.edgeSet.ncard : ℝ) ≤ C * n := by
  have hzero : ∀ n : ℕ, (n : ℝ) = 0 → (maxEdges n : ℝ) = 0 := by
    intro n hn
    have : n = 0 := by exact_mod_cast hn
    simp [this, maxEdges_zero]
  rw [Asymptotics.isBigO_nat_atTop_iff hzero]
  simp only [Real.norm_natCast]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n G hG => ?_⟩
    exact (Nat.cast_le.2 (le_maxEdges G hG)).trans (hC n)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    obtain ⟨G, hG, hmax⟩ := exists_maxEdges n
    simpa [hmax] using hC n G hG

end Erdos642
