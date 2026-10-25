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
# Erdős Problem 1017

*References:*
- [erdosproblems.com/1017](https://www.erdosproblems.com/1017)
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos,
  *The representation of a graph by set intersections*. Canadian J. Math. (1966), 106–112.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
- [GyKe17] Győri, Ervin and Keszegh, Balázs,
  *On the number of edge-disjoint triangles in $K_4$-free graphs*.
  Combinatorica (2017), 1113–1124.
- [Lo68] Lovász, L., *On covering of graphs*.
  Theory of Graphs (Proc. Colloq., Tihany, 1966) (1968), 231–236.
-/

@[expose] public section

namespace Erdos1017

open SimpleGraph

/-- The least uniform bound on the number of cliques in an edge partition of an
$n$-vertex, $k$-edge graph. For infeasible parameters the value is zero. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = k →
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m}

/-- Partitioning into individual edges gives the bound $f(n,k) \le k$. -/
@[category API, AMS 5]
theorem f_le (n k : ℕ) : f n k ≤ k := by
  classical
  apply Nat.sInf_le
  intro G hG
  obtain ⟨P, hP, hcard⟩ := G.exists_isCliqueEdgePartition_card_eq
  refine ⟨P, hP, ?_⟩
  simpa [hcard, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hG.le

/-- The infimum defining $f$ is an attained uniform bound. -/
@[category API, AMS 5]
theorem partition_card_le_f (n k : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = k) :
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ f n k := by
  classical
  have hne : {m : ℕ | ∀ H : SimpleGraph (Fin n), H.edgeSet.ncard = k →
      ∃ P : Finset (Finset (Fin n)), H.IsCliqueEdgePartition P ∧ P.card ≤ m}.Nonempty := by
    refine ⟨k, ?_⟩
    intro H hH
    obtain ⟨P, hP, hcard⟩ := H.exists_isCliqueEdgePartition_card_eq
    refine ⟨P, hP, ?_⟩
    simpa [hcard, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hH.le
  exact Nat.sInf_mem hne G hG

/-- A graph with no edges needs no cliques in its edge partition. -/
@[category test, AMS 5]
theorem f_zero (n : ℕ) : f n 0 = 0 := Nat.eq_zero_of_le_zero (f_le n 0)

/-- A proposed uniform bound is valid exactly when it is at least $f(n,k)$. -/
@[category API, AMS 5]
theorem f_le_iff (n k m : ℕ) : f n k ≤ m ↔
    ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = k →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m := by
  constructor
  · intro h G hG
    obtain ⟨P, hP, hcard⟩ := partition_card_le_f n k G hG
    exact ⟨P, hP, hcard.trans h⟩
  · intro h
    apply Nat.sInf_le
    exact h

/-- Impossible edge counts give the vacuous value zero and are excluded from the question. -/
@[category test, AMS 5]
theorem f_eq_zero_of_infeasible (n k : ℕ) (hk : n.choose 2 < k) : f n k = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [f_le_iff]
  intro G hG
  have hcard := G.card_edgeFinset_le_card_choose_two
  have : G.edgeFinset.card = k := by
    simpa [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hG
  simp only [Fintype.card_fin, this] at hcard
  omega

def erdos_1017.lower_bound.answer (n k : ℕ) : ℕ := by sorry

/-- Let $f(n,k)$ be such that every graph on $n$ vertices and $k$ edges can be partitioned
into at most $f(n,k)$ edge-disjoint complete graphs. Estimate $f(n,k)$ for $k>n^2/4$. -/
@[category research open, question value, AMS 5]
theorem erdos_1017.lower_bound :
    ∀ n k : ℕ, k ≤ n.choose 2 → n * n < 4 * k →
      erdos_1017.lower_bound.answer n k ≤ f n k := by
  sorry

def erdos_1017.upper_bound.answer (n k : ℕ) : ℕ := by sorry

/-- Estimate an upper bound for $f(n,k)$, the worst-case number of complete subgraphs
needed to partition the edges of an $n$-vertex, $k$-edge graph, for
$n^2/4 < k \le \binom{n}{2}$. -/
@[category research open, question value, AMS 5]
theorem erdos_1017.upper_bound :
    ∀ n k : ℕ, k ≤ n.choose 2 → n * n < 4 * k →
      f n k ≤ erdos_1017.upper_bound.answer n k := by
  sorry

end Erdos1017
